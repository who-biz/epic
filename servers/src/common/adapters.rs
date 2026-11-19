// Copyright 2026 The Epic Cash Developers
// Copyright 2020 The Grin Developers
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Adapters connecting new block, new transaction, and accepted transaction
//! events to consumers of those events.

use crate::util::RwLock;
use std::fs::File;
use std::path::PathBuf;
use std::sync::{Arc, Weak};
use std::thread;
use std::time::{Duration as StdDuration, Instant};

use crate::chain::{self, BlockStatus, ChainAdapter, Options, SyncState, SyncStatus};
use crate::common::hooks::{ChainEvents, NetEvents};
use crate::common::types::{ChainValidationMode, DandelionEpoch, ServerConfig};
use crate::core::core::hash::{Hash, Hashed};
use crate::core::core::transaction::Transaction;
use crate::core::core::{BlockHeader, BlockSums, CompactBlock};
use crate::core::pow::Difficulty;
use crate::core::{core, global};
use crate::p2p;
use crate::p2p::types::PeerInfo;
use crate::pool::{self, BlockChain, PoolAdapter};
use crate::util::OneTime;
use chrono::prelude::*;
use chrono::Duration;
use rand::prelude::*;
use std::collections::{HashMap, HashSet, VecDeque};
use std::sync::Mutex;

/// Force full pow verification this many blocks from chaintip
pub const POW_VERIFICATION_THRESHOLD: u64 = 1000;

fn forced_pow_threshold(network_height: u64) -> u64 {
	network_height.saturating_sub(POW_VERIFICATION_THRESHOLD)
}

fn should_skip_pow(config: &ServerConfig, checkpointed: bool, below_tip_window: bool) -> bool {
	config.skip_pow_validation.unwrap_or(false)
		&& (checkpointed
			|| (config.chain_type != global::ChainTypes::Mainnet
				&& config.disable_checkpoints.unwrap_or(false)
				&& below_tip_window))
}

fn is_bad_txhashset_data(error: &chain::Error) -> bool {
	matches!(
		error,
		chain::Error::InvalidBlockProof(_)
			| chain::Error::InvalidRoot
			| chain::Error::InvalidMMRSize
			| chain::Error::Secp(_)
			| chain::Error::AlreadySpent(_)
			| chain::Error::DuplicateCommitment(_)
			| chain::Error::ImmatureCoinbase
			| chain::Error::MerkleProof
			| chain::Error::OutputNotFound
			| chain::Error::RangeproofNotFound
			| chain::Error::TxKernelNotFound
			| chain::Error::OutputSpent
			| chain::Error::InvalidTxHashSet(_)
			| chain::Error::Transaction(_)
			| chain::Error::Committed(_)
	)
}

/// Ignore block broadcasts from chaintip, until we are less than
/// this many blocks from chaintip, while syncing
pub const BLOCK_BROADCAST_IGNORE_THRESHOLD: u64 = 200;

/// Ignore block broadcasts from chaintip, until we are less than
/// this many blocks from chaintip, while syncing
pub const HEADER_BROADCAST_IGNORE_THRESHOLD: u64 = 200;

const COMPACT_REQUEST_TIMEOUT: StdDuration = StdDuration::from_secs(10);
const COMPACT_REQUEST_LIFETIME: StdDuration = StdDuration::from_secs(120);
const MAX_COMPACT_REQUESTS: usize = 1_024;
const MAX_COMPACT_REQUEST_CANDIDATES: usize = 32;

type CompactRequestKey = (Hash, Hash);

fn compact_request_key(header: &BlockHeader) -> CompactRequestKey {
	(header.hash(), header.pre_pow().hash())
}

#[derive(Debug, PartialEq)]
enum CompactAnnouncement {
	Validate,
	Request(p2p::PeerAddr),
	Ignore,
}

struct CompactRequest {
	candidates: VecDeque<p2p::PeerAddr>,
	tried: HashSet<p2p::PeerAddr>,
	selected: Option<(p2p::PeerAddr, Instant)>,
	validating: bool,
	processing: bool,
	created: Instant,
}

struct CompactRequestTracker {
	requests: HashMap<CompactRequestKey, CompactRequest>,
}

impl CompactRequestTracker {
	fn new() -> Self {
		Self {
			requests: HashMap::with_capacity(MAX_COMPACT_REQUESTS),
		}
	}

	fn cleanup(&mut self, now: Instant) {
		self.requests.retain(|_, request| {
			request.processing || now.duration_since(request.created) < COMPACT_REQUEST_LIFETIME
		});
	}

	fn select_next(request: &mut CompactRequest, now: Instant) -> Option<p2p::PeerAddr> {
		while let Some(peer) = request.candidates.pop_front() {
			if request.tried.insert(peer) {
				request.selected = Some((peer, now));
				return Some(peer);
			}
		}
		None
	}

	fn announce(
		&mut self,
		key: CompactRequestKey,
		peer: p2p::PeerAddr,
		now: Instant,
	) -> CompactAnnouncement {
		self.cleanup(now);
		if let Some(request) = self.requests.get_mut(&key) {
			if !request.tried.contains(&peer)
				&& !request.candidates.contains(&peer)
				&& request.candidates.len() < MAX_COMPACT_REQUEST_CANDIDATES
			{
				request.candidates.push_back(peer);
			}
			if !request.validating && !request.processing {
				if request
					.selected
					.map_or(false, |(_, requested)| now.duration_since(requested) >= COMPACT_REQUEST_TIMEOUT)
				{
					request.selected = None;
				}
				if request.selected.is_none() {
					return Self::select_next(request, now)
						.map_or(CompactAnnouncement::Ignore, CompactAnnouncement::Request);
				}
			}
			return CompactAnnouncement::Ignore;
		}

		if self.requests.len() >= MAX_COMPACT_REQUESTS {
			if let Some(oldest) = self
				.requests
				.iter()
				.filter(|(_, request)| !request.processing)
				.min_by_key(|(_, request)| request.created)
				.map(|(key, _)| *key)
			{
				self.requests.remove(&oldest);
			} else {
				return CompactAnnouncement::Ignore;
			}
		}

		self.requests.insert(
			key,
			CompactRequest {
				candidates: VecDeque::from([peer]),
				tried: HashSet::new(),
				selected: None,
				validating: true,
				processing: false,
				created: now,
			},
		);
		CompactAnnouncement::Validate
	}

	fn validated(&mut self, key: CompactRequestKey, now: Instant) -> Option<p2p::PeerAddr> {
		let request = self.requests.get_mut(&key)?;
		request.validating = false;
		Self::select_next(request, now)
	}

	fn validation_failed(&mut self, key: CompactRequestKey) {
		self.requests.remove(&key);
	}

	fn begin_response(&mut self, key: CompactRequestKey, peer: p2p::PeerAddr) -> bool {
		if let Some(request) = self.requests.get_mut(&key) {
			if request.selected.map(|(selected, _)| selected) == Some(peer) && !request.processing {
				request.processing = true;
				return true;
			}
		}
		false
	}

	fn selected_failed(
		&mut self,
		key: CompactRequestKey,
		peer: p2p::PeerAddr,
		now: Instant,
	) -> Option<p2p::PeerAddr> {
		let request = self.requests.get_mut(&key)?;
		if request.selected.map(|(selected, _)| selected) != Some(peer) {
			return None;
		}
		request.processing = false;
		request.selected = None;
		Self::select_next(request, now)
	}

	fn complete(&mut self, key: CompactRequestKey) {
		self.requests.remove(&key);
	}

	fn remove_hash(&mut self, hash: Hash) {
		self.requests.retain(|(request_hash, _), _| *request_hash != hash);
	}

	fn clear(&mut self) {
		self.requests.clear();
	}

	fn maintain<F>(
		&mut self,
		now: Instant,
		mut connected: F,
	) -> Vec<(CompactRequestKey, p2p::PeerAddr)>
	where
		F: FnMut(p2p::PeerAddr) -> bool,
	{
		self.cleanup(now);
		let mut requests = vec![];
		for (key, request) in &mut self.requests {
			if request.validating || request.processing {
				continue;
			}
			if request.selected.map_or(false, |(peer, requested)| {
				!connected(peer) || now.duration_since(requested) >= COMPACT_REQUEST_TIMEOUT
			}) {
				request.selected = None;
			}
			while request.selected.is_none() {
				match Self::select_next(request, now) {
					Some(peer) if connected(peer) => {
						requests.push((*key, peer));
						break;
					}
					Some(_) => request.selected = None,
					None => break,
				}
			}
		}
		requests
	}
}

/// Implementation of the NetAdapter for the . Gets notified when new
/// blocks and transactions are received and forwards to the chain and pool
/// implementations.
pub struct NetToChainAdapter<B, P>
where
	B: BlockChain,
	P: PoolAdapter,
{
	sync_state: Arc<SyncState>,
	chain: Weak<chain::Chain>,
	tx_pool: Arc<RwLock<pool::TransactionPool<B, P>>>,
	peers: OneTime<Weak<p2p::Peers>>,
	config: ServerConfig,
	hooks: Vec<Box<dyn NetEvents + Send + Sync>>,
	compact_block_requests: Arc<Mutex<CompactRequestTracker>>,
}

impl<B, P> p2p::ChainAdapter for NetToChainAdapter<B, P>
where
	B: BlockChain,
	P: PoolAdapter,
{
	fn sync_status(&self) -> SyncStatus {
		self.sync_state.status()
	}

	fn check_compact_block_requests(&self) {
		if self.sync_state.status() != SyncStatus::NoSync {
			self.compact_block_requests.lock().unwrap().clear();
			return;
		}
		let peers = self.peers();
		let requests = self
			.compact_block_requests
			.lock()
			.unwrap()
			.maintain(Instant::now(), |peer| peers.is_connected(peer));
		for (key, peer) in requests {
			self.request_compact_block(key, peer);
		}
	}

	fn total_difficulty(&self) -> Result<Difficulty, chain::Error> {
		Ok(self.chain().head()?.total_difficulty)
	}

	fn total_height(&self) -> Result<u64, chain::Error> {
		Ok(self.chain().head()?.height)
	}

	fn total_header_height(&self) -> Result<u64, chain::Error> {
		Ok(self.chain().header_head()?.height)
	}

	fn get_transaction(&self, kernel_hash: Hash) -> Option<core::Transaction> {
		self.tx_pool.read().retrieve_tx_by_kernel_hash(kernel_hash)
	}

	fn tx_kernel_received(
		&self,
		kernel_hash: Hash,
		peer_info: &PeerInfo,
	) -> Result<bool, chain::Error> {
		// nothing much we can do with a new transaction while syncing
		if self.sync_state.is_syncing() {
			return Ok(true);
		}

		let tx = self.tx_pool.read().retrieve_tx_by_kernel_hash(kernel_hash);

		if tx.is_none() {
			self.request_transaction(kernel_hash, peer_info);
		}
		Ok(true)
	}

	fn transaction_received(
		&self,
		tx: core::Transaction,
		stem: bool,
		peer_info: &PeerInfo,
	) -> Result<bool, chain::Error> {
		// nothing much we can do with a new transaction while syncing
		if self.sync_state.is_syncing() {
			return Ok(true);
		}

		let source = pool::TxSource::Broadcast;

		let header = self.chain().head_header()?;

		for hook in &self.hooks {
			let _ = hook.on_transaction_received(&tx, &peer_info);
		}

		let tx_hash = tx.hash();

		let mut tx_pool = self.tx_pool.write();
		match tx_pool.add_to_pool(source, tx, stem, &header) {
			Ok(_) => Ok(true),
			Err(e) => {
				debug!("Transaction {} rejected: {:?}", tx_hash, e);
				Ok(false)
			}
		}
	}

	fn block_received(
		&self,
		b: core::Block,
		peer_info: &PeerInfo,
		opts: chain::Options,
	) -> Result<bool, chain::Error> {
		// TODO: guard against panic on unwrap, in case someone changes this constant
		if self.sync_state.is_syncing() {
			if b.header.height.clone()
				> (self.chain().head()?.height + BLOCK_BROADCAST_IGNORE_THRESHOLD)
			{
				warn!(
					"Ignoring full block {}, height({}), delivered during sync from peer {}",
					b.hash(),
					b.header.height.clone(),
					peer_info.addr
				);
				return Ok(true);
			}
		}

		let hash = b.hash();
		if self.chain().block_exists(hash)? {
			self.compact_block_requests.lock().unwrap().remove_hash(hash);
			return Ok(true);
		}
		debug!(
			"Received block {} at {} from {} [in/out/kern: {}/{}/{}] going to process.",
			b.hash(),
			b.header.height,
			peer_info.addr,
			b.inputs().len(),
			b.outputs().len(),
			b.kernels().len(),
		);
		let result = self.process_block(b, peer_info, opts);
		if self.chain().block_exists(hash).unwrap_or(false) {
			self.compact_block_requests.lock().unwrap().remove_hash(hash);
		}
		result
	}

	fn compact_block_received(
		&self,
		cb: core::CompactBlock,
		peer_info: &PeerInfo,
	) -> Result<bool, chain::Error> {
		if self.sync_state.is_syncing() {
			if cb.header.height.clone()
				> (self.chain().head()?.height + BLOCK_BROADCAST_IGNORE_THRESHOLD)
			{
				debug!(
					"Ignoring compact block {}, height({}), delivered during sync",
					cb.hash(),
					cb.header.height.clone()
				);
				return Ok(true);
			}
		}

		let cb_hash = cb.hash();

		// No need to process this compact block if we have previously accepted the _full block_.
		if self.chain().block_exists(cb_hash)? {
			self.compact_block_requests.lock().unwrap().remove_hash(cb_hash);
			return Ok(true);
		}

		let request_key = compact_request_key(&cb.header);
		if !self
			.compact_block_requests
			.lock()
			.unwrap()
			.begin_response(request_key, peer_info.addr)
		{
			// Only the peer selected for this exact header may satisfy the request.
			return Ok(true);
		}

		let result = (|| -> Result<bool, chain::Error> {
			debug!(
				"Received compact_block {} at {} from {} [out/kern/kern_ids: {}/{}/{}] going to process.",
				cb_hash.clone(),
				cb.header.height,
				peer_info.addr,
				cb.out_full().len(),
				cb.kern_full().len(),
				cb.kern_ids().len(),
			);

			if cb.kern_ids().is_empty() {
				// push the freshly hydrated block through the chain pipeline
				match core::Block::hydrate_from(cb, vec![]) {
					Ok(block) => {
						if !self.sync_state.is_syncing() {
							for hook in &self.hooks {
								let _ = hook.on_block_received(&block, &peer_info.addr);
							}
						}
						self.process_block(block, peer_info, chain::Options::NONE)
					}
					Err(e) => {
						debug!("Invalid hydrated block {}: {:?}", cb_hash, e);
						Ok(false)
					}
				}
			} else {
				// check at least the header is valid before hydrating
				if let Err(e) = self
					.chain()
					.process_block_header(&cb.header, chain::Options::NONE)
				{
					debug!("Invalid compact block header {}: {:?}", cb_hash, e);
					return Ok(!e.is_bad_data());
				}
				peer_info.update_validated_tip(
					cb.header.height,
					cb.header.total_difficulty(),
					cb.header.hash(),
				);

				let (txs, missing_short_ids) = {
					self.tx_pool
						.read()
						.retrieve_transactions(cb.hash(), cb.nonce, cb.kern_ids())
				};

				debug!(
					"compact_block_received: txs from tx pool - {}, (unknown kern_ids: {})",
					txs.len(),
					missing_short_ids.len(),
				);

				// If we have missing kernels then we know we cannot hydrate this compact block.
				if missing_short_ids.len() > 0 {
					self.request_block(&cb.header, peer_info, chain::Options::NONE);
					return Ok(true);
				}

				let block = match core::Block::hydrate_from(cb.clone(), txs) {
					Ok(block) => {
						if !self.sync_state.is_syncing() {
							for hook in &self.hooks {
								let _ = hook.on_block_received(&block, &peer_info.addr);
							}
						}
						block
					}
					Err(e) => {
						debug!("Invalid hydrated block {}: {:?}", cb.hash(), e);
						return Ok(false);
					}
				};

				if let Ok(prev) = self.chain().get_previous_header(&cb.header) {
					if block.validate(&prev.total_kernel_offset).is_ok() {
						debug!("successfully hydrated block from tx pool!");
						self.process_block(block, peer_info, chain::Options::NONE)
					} else {
						if self.sync_state.status() == SyncStatus::NoSync {
							debug!("adapter: block invalid after hydration, requesting full block");
							self.request_block(&cb.header, peer_info, chain::Options::NONE);
							Ok(true)
						} else {
							debug!("block invalid after hydration, ignoring it, cause still syncing");
							Ok(true)
						}
					}
				} else {
					debug!("failed to retrieve previous block header (still syncing?)");
					Ok(true)
				}
			}
		})();

		let retry = match &result {
			Ok(true) => {
				self.compact_block_requests.lock().unwrap().complete(request_key);
				None
			}
			Ok(false) | Err(_) => self
				.compact_block_requests
				.lock()
				.unwrap()
				.selected_failed(request_key, peer_info.addr, Instant::now()),
		};
		if let Some(peer) = retry {
			self.request_compact_block(request_key, peer);
		}
		result
	}

	fn header_received(
		&self,
		bh: core::BlockHeader,
		peer_info: &PeerInfo,
	) -> Result<bool, chain::Error> {
		// Keep new headers synced except when in HeaderSync mode.
		if matches!(self.sync_state.status(), SyncStatus::HeaderSync { .. }) {
			return Ok(true);
		}

		// No need to process this header if we have previously accepted the _full block_.
		let hash = bh.hash();
		if self.chain().block_exists(hash)? {
			self.compact_block_requests.lock().unwrap().remove_hash(hash);
			return Ok(true);
		}

		let request_key = if self.sync_state.status() == SyncStatus::NoSync {
			let key = compact_request_key(&bh);
			let announcement = self
				.compact_block_requests
				.lock()
				.unwrap()
				.announce(key, peer_info.addr, Instant::now());
			match announcement {
				CompactAnnouncement::Validate => Some(key),
				CompactAnnouncement::Request(peer) => {
					self.request_compact_block(key, peer);
					return Ok(true);
				}
				CompactAnnouncement::Ignore => return Ok(true),
			}
		} else {
			None
		};

		if !self.sync_state.is_syncing() {
			for hook in &self.hooks {
				let _ = hook.on_header_received(&bh, &peer_info.addr);
			}
		}

		// pushing the new block header through the header chain pipeline
		// we will go ask for the block if this is a new header
		let res = self.chain().process_block_header(&bh, chain::Options::NONE);

		if let Err(e) = res {
			if let Some(key) = request_key {
				self.compact_block_requests.lock().unwrap().validation_failed(key);
			}

			debug!("Block header {} refused by chain: {:?}", bh.hash(), e);
			if e.is_bad_data() {
				return Ok(false);
			} else {
				// we got an error when trying to process the block header
				// but nothing serious enough to need to ban the peer upstream
				return Err(e);
			}
		}

		// we have successfully processed a block header
		peer_info.update_validated_tip(bh.height, bh.total_difficulty(), bh.hash());
		if let Some(key) = request_key {
			let peer = self
				.compact_block_requests
				.lock()
				.unwrap()
				.validated(key, Instant::now());
			if let Some(peer) = peer {
				self.request_compact_block(key, peer);
			}
		}

		Ok(true)
	}

	// if headers are empty or refused, then peer is banned
	fn headers_received(
		&self,
		bhs: &[core::BlockHeader],
		peer_info: &PeerInfo,
	) -> Result<bool, chain::Error> {
		if bhs.len() == 0 {
			//peer is banned
			return Ok(false);
		}
		let start_time = Utc::now().timestamp();
		info!(
			"Validate {} block headers from {}",
			bhs.len(),
			peer_info.addr
		);

		let mut ctx_option = Options::SYNC;
		let mut within_checkpointed_range = true;

		for header in bhs {
			match self.chain().check_header_against_checkpoints(header) {
				Ok(in_range) => {
					within_checkpointed_range &= in_range;
				}
				Err(e) => {
					return Err(e);
				}
			}
		}

		if should_skip_pow(&self.config, within_checkpointed_range, true) {
			ctx_option = Options::SKIP_POW;
		}

		match self.chain().sync_block_headers(bhs, ctx_option) {
			Ok(_) => {
				if let Some(header) = bhs.iter().max_by_key(|header| header.total_difficulty()) {
					peer_info.update_validated_tip(
						header.height,
						header.total_difficulty(),
						header.hash(),
					);
				}
				info!(
					"------------ Validation required: {:?} sec ------------",
					Utc::now().timestamp() - start_time,
				);
				return Ok(true);
			}
			Err(e) => {
				debug!(
					"Block headers refused by chain: {:?} {}",
					e,
					e.is_bad_data()
				);
				if e.is_bad_data() {
					return Ok(false);
				} else {
					Err(e)
				}
			}
		}
	}

	fn locate_headers(
		&self,
		locator: &[Hash],
		offset: &u8,
	) -> Result<Vec<core::BlockHeader>, chain::Error> {
		debug!("locator: {:?}", locator);

		let header = match self.find_common_header(locator) {
			Some(header) => header,
			None => return Ok(vec![]),
		};

		let max_height = self.chain().header_head()?.height;

		let header_pmmr = self.chain().header_pmmr();
		let header_pmmr = header_pmmr.read();

		// looks like we know one, getting as many following headers as allowed
		let hh = header.height;
		let offset: u64 = offset.clone() as u64 * p2p::MAX_BLOCK_HEADERS as u64;
		debug!("Locate headers with offset request: {:?}", offset);

		let mut headers = vec![];
		for h in (hh + 1)..=(hh + (p2p::MAX_BLOCK_HEADERS as u64)) {
			if h + offset > max_height {
				break;
			}

			if let Ok(hash) = header_pmmr.get_header_hash_by_height(h + offset) {
				let header = self.chain().get_block_header(&hash)?;
				headers.push(header);
			} else {
				error!("Failed to locate headers successfully.");
				break;
			}
		}

		debug!("returning headers: {}", headers.len());

		Ok(headers)
	}

	/// Gets a full block by its hash.
	fn get_block(&self, h: Hash) -> Option<core::Block> {
		let b = self.chain().get_block(&h);
		match b {
			Ok(b) => Some(b),
			_ => None,
		}
	}

	/// Provides a reading view into the current txhashset state as well as
	/// the required indexes for a consumer to rewind to a consistent state
	/// at the provided block hash.
	fn txhashset_read(&self, h: Hash) -> Option<p2p::TxHashSetRead> {
		match self.chain().txhashset_read(h.clone()) {
			Ok((output_index, kernel_index, reader)) => Some(p2p::TxHashSetRead {
				output_index,
				kernel_index,
				reader,
			}),
			Err(e) => {
				warn!("Couldn't produce txhashset data for block {}: {:?}", h, e);
				None
			}
		}
	}

	fn txhashset_archive_header(&self) -> Result<core::BlockHeader, chain::Error> {
		self.chain().txhashset_archive_header()
	}

	fn txhashset_receive_ready(&self) -> bool {
		match self.sync_state.status() {
			SyncStatus::TxHashsetDownload { .. } => true,
			_ => false,
		}
	}

	fn txhashset_download_update(
		&self,
		start_time: DateTime<Utc>,
		downloaded_size: u64,
		total_size: u64,
	) -> bool {
		match self.sync_state.status() {
			SyncStatus::TxHashsetDownload {
				update_time: old_update_time,
				downloaded_size: old_downloaded_size,
				..
			} => self
				.sync_state
				.update_txhashset_download(SyncStatus::TxHashsetDownload {
					start_time,
					prev_update_time: old_update_time,
					update_time: Utc::now(),
					prev_downloaded_size: old_downloaded_size,
					downloaded_size,
					total_size,
				}),
			_ => false,
		}
	}

	/// Writes a reading view on a txhashset state that's been provided to us.
	/// If we're willing to accept that new state, the data stream will be
	/// read as a zip file, unzipped and the resulting state files should be
	/// rewound to the provided indexes.
	fn txhashset_write(
		&self,
		h: Hash,
		txhashset_data: File,
		_peer_info: &PeerInfo,
	) -> Result<bool, chain::Error> {
		// check status again after download, in case 2 txhashsets made it somehow
		if let SyncStatus::TxHashsetDownload { .. } = self.sync_state.status() {
		} else {
			return Ok(false);
		}

		match self
			.chain()
			.txhashset_write(h, txhashset_data, self.sync_state.as_ref())
		{
			Ok(is_bad_data) => {
				if is_bad_data {
					self.chain().clean_txhashset_sandbox();
					error!("Failed to save Txhashset archive: bad data");
					self.sync_state.set_sync_error(
						chain::Error::TxHashSetErr("bad Txhashset data".to_string()).into(),
					);
				} else {
					info!("Received valid txhashset data for {}.", h);
				}
				Ok(is_bad_data)
			}
			Err(e) => {
				let is_bad_data = is_bad_txhashset_data(&e);
				self.chain().clean_txhashset_sandbox();
				error!("Failed to save Txhashset archive: {}", e);
				self.sync_state.set_sync_error(e);
				Ok(is_bad_data)
			}
		}
	}

	fn get_tmp_dir(&self) -> PathBuf {
		self.chain().get_tmp_dir()
	}

	fn get_tmpfile_pathname(&self, tmpfile_name: String) -> PathBuf {
		self.chain().get_tmpfile_pathname(tmpfile_name)
	}
}

impl<B, P> NetToChainAdapter<B, P>
where
	B: BlockChain,
	P: PoolAdapter,
{
	/// Construct a new NetToChainAdapter instance
	pub fn new(
		sync_state: Arc<SyncState>,
		chain: Arc<chain::Chain>,
		tx_pool: Arc<RwLock<pool::TransactionPool<B, P>>>,
		config: ServerConfig,
		hooks: Vec<Box<dyn NetEvents + Send + Sync>>,
	) -> Self {
		NetToChainAdapter {
			sync_state,
			chain: Arc::downgrade(&chain),
			tx_pool,
			peers: OneTime::new(),
			config,
			hooks,
			compact_block_requests: Arc::new(Mutex::new(CompactRequestTracker::new())),
		}
	}

	/// Initialize a NetToChainAdaptor with reference to a Peers object.
	/// Should only be called once.
	pub fn init(&self, peers: Arc<p2p::Peers>) {
		self.peers.init(Arc::downgrade(&peers));
	}

	fn peers(&self) -> Arc<p2p::Peers> {
		self.peers
			.borrow()
			.upgrade()
			.expect("Failed to upgrade weak ref to our peers.")
	}

	fn chain(&self) -> Arc<chain::Chain> {
		self.chain
			.upgrade()
			.expect("Failed to upgrade weak ref to our chain.")
	}

	// Find the first locator hash that refers to a known header on our main chain.
	fn find_common_header(&self, locator: &[Hash]) -> Option<BlockHeader> {
		let header_pmmr = self.chain().header_pmmr();
		let header_pmmr = header_pmmr.read();

		for hash in locator {
			if let Ok(header) = self.chain().get_block_header(&hash) {
				if let Ok(hash_at_height) = header_pmmr.get_header_hash_by_height(header.height) {
					if let Ok(header_at_height) = self.chain().get_block_header(&hash_at_height) {
						if header.hash() == header_at_height.hash() {
							return Some(header);
						}
					}
				}
			}
		}
		None
	}

	// pushing the new block through the chain pipeline
	// remembering to reset the head if we have a bad block
	fn process_block(
		&self,
		b: core::Block,
		peer_info: &PeerInfo,
		opts: chain::Options,
	) -> Result<bool, chain::Error> {
		// We cannot process blocks earlier than the horizon so check for this here.
		{
			let head = self.chain().head()?;
			let horizon = head
				.height
				.saturating_sub(global::cut_through_horizon() as u64);
			if b.header.height < horizon {
				return Ok(true);
			}
		}

		let bhash = b.hash();
		let previous = self.chain().get_previous_header(&b.header);
		let within_checkpointed_range;
		let mut options = opts;

		let network_height = self.chain().header_head()?.height;
		// ensure we check proof-of-work for last (POW_VERIFICATION_THRESHOLD) blocks from network chaintip
		let check_pow_dyn_threshold = forced_pow_threshold(network_height);

		let outside_forced_pow_threshold = b.header.height < check_pow_dyn_threshold;

		match self.chain().check_header_against_checkpoints(&b.header) {
			Ok(in_range) => {
				within_checkpointed_range = in_range;
			}
			Err(e) => {
				return Err(e);
			}
		}

		if should_skip_pow(
			&self.config,
			within_checkpointed_range,
			outside_forced_pow_threshold,
		) {
			options = chain::Options::SKIP_POW;
		}

		let height = b.header.height;
		let total_difficulty = b.header.total_difficulty();
		match self.chain().process_block(b, options) {
			Ok(_) => {
				peer_info.update_validated_tip(height, total_difficulty, bhash.clone());
				self.validate_chain(bhash);
				self.check_compact();
				Ok(true)
			}
			Err(ref e) if e.is_bad_data() => {
				self.validate_chain(bhash);
				Ok(false)
			}
			Err(e) => {
				match e {
					chain::Error::Orphan => {
						if let Ok(previous) = previous {
							// make sure we did not miss the parent block
							if !self.chain().is_orphan(&previous.hash())
								&& !self.sync_state.is_syncing()
							{
								debug!(
									"Received an orphan block, checking the parent: {:}",
									previous.hash()
								);
								self.request_block(&previous, peer_info, chain::Options::NONE)
							}
						}
						Ok(true)
					}
					_ => {
						debug!("Block {} refused by chain: {}", bhash, e);
						Ok(true)
					}
				}
			}
		}
	}

	fn validate_chain(&self, bhash: Hash) {
		// If we are running in "validate the full chain every block" then
		// panic here if validation fails for any reason.
		// We are out of consensus at this point and want to track the problem
		// down as soon as possible.
		// Skip this if we are currently syncing (too slow).
		if self.config.chain_validation_mode == ChainValidationMode::EveryBlock
			&& self.chain().head().unwrap().height > 0
			&& !self.sync_state.is_syncing()
		{
			let now = Instant::now();

			debug!(
				"process_block: ***** validating full chain state at {}",
				bhash,
			);

			self.chain()
				.validate(true)
				.expect("chain validation failed, hard stop");

			debug!(
				"process_block: ***** done validating full chain state, took {}s",
				now.elapsed().as_secs(),
			);
		}
	}

	fn check_compact(&self) {
		// Skip compaction if we are syncing.
		if self.sync_state.is_syncing() {
			return;
		}

		// Roll the dice to trigger compaction at 1/COMPACTION_CHECK chance per block,
		// uses a different thread to avoid blocking the caller thread (likely a peer)
		let mut rng = rand::rng();
		if 0 == rng.random_range(0..global::COMPACTION_CHECK) {
			let chain = self.chain().clone();
			let _ = thread::Builder::new()
				.name("compactor".to_string())
				.spawn(move || {
					if let Err(e) = chain.compact() {
						error!("Could not compact chain: {:?}", e);
					}
				});
		}
	}

	fn request_transaction(&self, h: Hash, peer_info: &PeerInfo) {
		self.send_tx_request_to_peer(h, peer_info, |peer, h| peer.send_tx_request(h))
	}

	// After receiving a compact block if we cannot successfully hydrate
	// it into a full block then fallback to requesting the full block
	// from the same peer that gave us the compact block
	// consider additional peers for redundancy?
	fn request_block(&self, bh: &BlockHeader, peer_info: &PeerInfo, opts: Options) {
		self.send_block_request_to_peer(bh.hash(), peer_info, |peer, h| {
			peer.send_block_request(h, opts)
		})
	}

	fn request_compact_block(&self, key: CompactRequestKey, mut peer_addr: p2p::PeerAddr) {
		loop {
			match self.chain().block_exists(key.0) {
				Ok(true) => {
					self.compact_block_requests.lock().unwrap().complete(key);
					return;
				}
				Err(e) => {
					error!("Failed to check compact block {} before request: {:?}", key.0, e);
					return;
				}
				Ok(false) => {}
			}

			let sent = self
				.peers()
				.get_connected_peer(peer_addr)
				.map_or(false, |peer| match peer.send_compact_block_request(key.0) {
					Ok(_) => true,
					Err(e) => {
						debug!("Failed to request compact block {} from {}: {:?}", key.0, peer_addr, e);
						false
					}
				});
			if sent {
				return;
			}

			let next = self
				.compact_block_requests
				.lock()
				.unwrap()
				.selected_failed(key, peer_addr, Instant::now());
			match next {
				Some(peer) => peer_addr = peer,
				None => return,
			}
		}
	}

	fn send_tx_request_to_peer<F>(&self, h: Hash, peer_info: &PeerInfo, f: F)
	where
		F: Fn(&p2p::Peer, Hash) -> Result<(), p2p::Error>,
	{
		match self.peers().get_connected_peer(peer_info.addr) {
			None => debug!(
				"Can't send request to peer {:?}, not connected",
				peer_info.addr
			),
			Some(peer) => {
				if let Err(e) = f(&peer, h) {
					error!("send_tx_request_to_peer: failed: {:?}", e)
				}
			}
		}
	}

	fn send_block_request_to_peer<F>(&self, h: Hash, peer_info: &PeerInfo, f: F)
	where
		F: Fn(&p2p::Peer, Hash) -> Result<(), p2p::Error>,
	{
		match self.chain().block_exists(h) {
			Ok(false) => match self.peers().get_connected_peer(peer_info.addr) {
				None => debug!(
					"Can't send request to peer {:?}, not connected",
					peer_info.addr
				),
				Some(peer) => {
					if let Err(e) = f(&peer, h) {
						error!("Send block request to peer failed: {:?}", e)
					}
				}
			},
			Ok(true) => debug!("Send block request to peer. Block {} already known", h),
			Err(e) => error!(
				"Send block request to peer. failed to check block exists: {:?}",
				e
			),
		}
	}

}

/// Implementation of the ChainAdapter for the network. Gets notified when the
///  accepted a new block, asking the pool to update its state and
/// the network to broadcast the block
pub struct ChainToPoolAndNetAdapter<B, P>
where
	B: BlockChain,
	P: PoolAdapter,
{
	tx_pool: Arc<RwLock<pool::TransactionPool<B, P>>>,
	peers: OneTime<Weak<p2p::Peers>>,
	hooks: Vec<Box<dyn ChainEvents + Send + Sync>>,
}

impl<B, P> ChainAdapter for ChainToPoolAndNetAdapter<B, P>
where
	B: BlockChain,
	P: PoolAdapter,
{
	fn block_accepted(&self, b: &core::Block, status: BlockStatus, opts: Options) {
		// not broadcasting blocks received through sync
		if !opts.contains(chain::Options::SYNC) && !opts.contains(chain::Options::SKIP_POW) {
			for hook in &self.hooks {
				let _ = hook.on_block_accepted(b, &status);
			}
			// If we mined the block then we want to broadcast the compact block.
			// If we received the block from another node then broadcast "header first"
			// to minimize network traffic.
			if opts.contains(Options::MINE) {
				// propagate compact block out if we mined the block
				let cb: CompactBlock = b.clone().into();
				self.peers().broadcast_compact_block(&cb);
			} else {
				// "header first" propagation if we are not the originator of this block
				self.peers().broadcast_header(&b.header);
			}
		}

		// Reconcile the txpool against the new block *after* we have broadcast it too our peers.
		// This may be slow and we do not want to delay block propagation.
		// We only want to reconcile the txpool against the new block *if* total work has increased.
		let is_reorg = if let BlockStatus::Reorg(_) = status {
			true
		} else {
			false
		};
		if status == BlockStatus::Next || is_reorg {
			let mut tx_pool = self.tx_pool.write();

			let _ = tx_pool.reconcile_block(b);

			// First "age out" any old txs in the reorg_cache.
			let cutoff = Utc::now() - Duration::minutes(30);
			tx_pool.truncate_reorg_cache(cutoff);
		}

		if is_reorg {
			let _ = self.tx_pool.write().reconcile_reorg_cache(&b.header);
		}
	}
}

impl<B, P> ChainToPoolAndNetAdapter<B, P>
where
	B: BlockChain,
	P: PoolAdapter,
{
	/// Construct a ChainToPoolAndNetAdapter instance.
	pub fn new(
		tx_pool: Arc<RwLock<pool::TransactionPool<B, P>>>,
		hooks: Vec<Box<dyn ChainEvents + Send + Sync>>,
	) -> Self {
		ChainToPoolAndNetAdapter {
			tx_pool,
			peers: OneTime::new(),
			hooks,
		}
	}

	/// Initialize a ChainToPoolAndNetAdapter instance with handle to a Peers
	/// object. Should only be called once.
	pub fn init(&self, peers: Arc<p2p::Peers>) {
		self.peers.init(Arc::downgrade(&peers));
	}

	fn peers(&self) -> Arc<p2p::Peers> {
		self.peers
			.borrow()
			.upgrade()
			.expect("Failed to upgrade weak ref to our peers.")
	}
}

/// Adapter between the transaction pool and the network, to relay
/// transactions that have been accepted.
pub struct PoolToNetAdapter {
	peers: OneTime<Weak<p2p::Peers>>,
	dandelion_epoch: Arc<RwLock<DandelionEpoch>>,
}

/// Adapter between the Dandelion monitor and the current Dandelion "epoch".
pub trait DandelionAdapter: Send + Sync {
	/// Is the node stemming (or fluffing) transactions in the current epoch?
	fn is_stem(&self) -> bool;

	/// Is the current Dandelion epoch expired?
	fn is_expired(&self) -> bool;

	/// Transition to the next Dandelion epoch (new stem/fluff state, select new relay peer).
	fn next_epoch(&self);
}

impl DandelionAdapter for PoolToNetAdapter {
	fn is_stem(&self) -> bool {
		self.dandelion_epoch.read().is_stem()
	}

	fn is_expired(&self) -> bool {
		self.dandelion_epoch.read().is_expired()
	}

	fn next_epoch(&self) {
		self.dandelion_epoch.write().next_epoch(&self.peers());
	}
}

impl pool::PoolAdapter for PoolToNetAdapter {
	fn tx_accepted(&self, entry: &pool::PoolEntry) {
		self.peers().broadcast_transaction(&entry.tx);
	}

	fn stem_tx_accepted(&self, entry: &pool::PoolEntry) -> Result<(), pool::PoolError> {
		// Take write lock on the current epoch.
		// We need to be able to update the current relay peer if not currently connected.
		let mut epoch = self.dandelion_epoch.write();

		// If "stem" epoch attempt to relay the tx to the next Dandelion relay.
		// Fallback to immediately fluffing the tx if we cannot stem for any reason.
		// If "fluff" epoch then nothing to do right now (fluff via Dandelion monitor).
		// If node is configured to always stem our (pushed via api) txs then do so.
		if epoch.is_stem() || (entry.src.is_pushed() && epoch.always_stem_our_txs()) {
			if let Some(peer) = epoch.relay_peer(&self.peers()) {
				match peer.send_stem_transaction(&entry.tx) {
					Ok(_) => {
						info!("Stemming this epoch, relaying to next peer.");
						Ok(())
					}
					Err(e) => {
						error!("Stemming tx failed. Fluffing. {:?}", e);
						Err(pool::PoolError::DandelionError)
					}
				}
			} else {
				error!("No relay peer. Fluffing.");
				Err(pool::PoolError::DandelionError)
			}
		} else {
			info!("Fluff epoch. Aggregating stem tx(s). Will fluff via Dandelion monitor.");
			Ok(())
		}
	}
}

impl PoolToNetAdapter {
	/// Create a new pool to net adapter
	pub fn new(config: pool::DandelionConfig) -> PoolToNetAdapter {
		PoolToNetAdapter {
			peers: OneTime::new(),
			dandelion_epoch: Arc::new(RwLock::new(DandelionEpoch::new(config))),
		}
	}

	/// Setup the p2p server on the adapter
	pub fn init(&self, peers: Arc<p2p::Peers>) {
		self.peers.init(Arc::downgrade(&peers));
	}

	fn peers(&self) -> Arc<p2p::Peers> {
		self.peers
			.borrow()
			.upgrade()
			.expect("Failed to upgrade weak ref to our peers.")
	}
}

/// Implements the view of the  required by the TransactionPool to
/// operate. Mostly needed to break any direct lifecycle or implementation
/// dependency between the pool and the chain.
#[derive(Clone)]
pub struct PoolToChainAdapter {
	chain: OneTime<Weak<chain::Chain>>,
}

impl PoolToChainAdapter {
	/// Create a new pool adapter
	pub fn new() -> PoolToChainAdapter {
		PoolToChainAdapter {
			chain: OneTime::new(),
		}
	}

	/// Set the pool adapter's chain. Should only be called once.
	pub fn set_chain(&self, chain_ref: Arc<chain::Chain>) {
		self.chain.init(Arc::downgrade(&chain_ref));
	}

	fn chain(&self) -> Arc<chain::Chain> {
		self.chain
			.borrow()
			.upgrade()
			.expect("Failed to upgrade the weak ref to our chain.")
	}
}

impl pool::BlockChain for PoolToChainAdapter {
	fn chain_head(&self) -> Result<BlockHeader, pool::PoolError> {
		self.chain()
			.head_header()
			.map_err(|_| pool::PoolError::Other(format!("failed to get head_header")))
	}

	fn get_block_header(&self, hash: &Hash) -> Result<BlockHeader, pool::PoolError> {
		self.chain()
			.get_block_header(hash)
			.map_err(|_| pool::PoolError::Other(format!("failed to get block_header")))
	}

	fn get_block_sums(&self, hash: &Hash) -> Result<BlockSums, pool::PoolError> {
		self.chain()
			.get_block_sums(hash)
			.map_err(|_| pool::PoolError::Other(format!("failed to get block_sums")))
	}

	fn validate_tx(&self, tx: &Transaction) -> Result<(), pool::PoolError> {
		self.chain()
			.validate_tx(tx)
			.map_err(|_| pool::PoolError::Other(format!("failed to validate tx")))
	}

	fn verify_coinbase_maturity(&self, tx: &Transaction) -> Result<(), pool::PoolError> {
		self.chain()
			.verify_coinbase_maturity(tx)
			.map_err(|_| pool::PoolError::ImmatureCoinbase)
	}

	fn verify_tx_lock_height(&self, tx: &Transaction) -> Result<(), pool::PoolError> {
		self.chain()
			.verify_tx_lock_height(tx)
			.map_err(|_| pool::PoolError::ImmatureTransaction)
	}
}

#[cfg(test)]
mod test {
	use super::*;

	fn peer(port: u16) -> p2p::PeerAddr {
		p2p::PeerAddr(format!("127.0.0.1:{}", port).parse().unwrap())
	}

	fn request_key(value: u64) -> CompactRequestKey {
		(
			Hash::from_vec(&value.to_le_bytes()),
			Hash::from_vec(&value.wrapping_add(1).to_le_bytes()),
		)
	}

	#[test]
	fn compact_announcements_create_one_initial_request() {
		let now = Instant::now();
		let key = request_key(1);
		let mut tracker = CompactRequestTracker::new();
		assert_eq!(tracker.announce(key, peer(1), now), CompactAnnouncement::Validate);
		for port in 2..10 {
			assert_eq!(tracker.announce(key, peer(port), now), CompactAnnouncement::Ignore);
		}
		assert_eq!(tracker.validated(key, now), Some(peer(1)));
		assert_eq!(tracker.announce(key, peer(10), now), CompactAnnouncement::Ignore);
		assert_eq!(
			tracker.announce((key.0, request_key(2).1), peer(10), now),
			CompactAnnouncement::Validate
		);
	}

	#[test]
	fn compact_request_timeout_selects_one_fallback() {
		let now = Instant::now();
		let key = request_key(2);
		let mut tracker = CompactRequestTracker::new();
		assert_eq!(tracker.announce(key, peer(1), now), CompactAnnouncement::Validate);
		assert_eq!(tracker.announce(key, peer(2), now), CompactAnnouncement::Ignore);
		assert_eq!(tracker.announce(key, peer(3), now), CompactAnnouncement::Ignore);
		assert_eq!(tracker.validated(key, now), Some(peer(1)));

		let retry_at = now + COMPACT_REQUEST_TIMEOUT;
		assert_eq!(tracker.maintain(retry_at, |_| true), vec![(key, peer(2))]);
		assert!(tracker.maintain(retry_at, |_| true).is_empty());
		assert_eq!(
			tracker.maintain(retry_at + StdDuration::from_secs(1), |addr| addr != peer(2)),
			vec![(key, peer(3))]
		);
	}

	#[test]
	fn compact_responses_have_one_processing_winner_and_invalid_fallback() {
		let now = Instant::now();
		let key = request_key(3);
		let mut tracker = CompactRequestTracker::new();
		assert_eq!(tracker.announce(key, peer(1), now), CompactAnnouncement::Validate);
		assert_eq!(tracker.announce(key, peer(2), now), CompactAnnouncement::Ignore);
		assert_eq!(tracker.validated(key, now), Some(peer(1)));
		assert!(tracker.begin_response(key, peer(1)));
		assert!(!tracker.begin_response(key, peer(1)));
		assert!(!tracker.begin_response(key, peer(2)));
		assert_eq!(tracker.selected_failed(key, peer(1), now), Some(peer(2)));
		assert!(tracker.begin_response(key, peer(2)));
		tracker.complete(key);
		assert!(!tracker.begin_response(key, peer(2)));
	}

	#[test]
	fn compact_request_state_is_bounded_and_expires() {
		let now = Instant::now();
		let mut tracker = CompactRequestTracker::new();
		let key = request_key(9);
		tracker.announce(key, peer(1), now);
		for port in 2..100 {
			tracker.announce(key, peer(port), now);
		}
		assert_eq!(
			tracker.requests.get(&key).unwrap().candidates.len(),
			MAX_COMPACT_REQUEST_CANDIDATES
		);
		for value in 0..MAX_COMPACT_REQUESTS + 100 {
			tracker.announce(request_key(value as u64 + 10), peer(1), now);
		}
		assert_eq!(tracker.requests.len(), MAX_COMPACT_REQUESTS);
		tracker.maintain(now + COMPACT_REQUEST_LIFETIME, |_| true);
		assert!(tracker.requests.is_empty());
	}

	#[test]
	fn forced_pow_threshold_saturates_below_window() {
		assert_eq!(forced_pow_threshold(0), 0);
		assert_eq!(forced_pow_threshold(POW_VERIFICATION_THRESHOLD + 1), 1);
	}

	#[test]
	fn default_pow_policy_skips_only_checkpointed_history() {
		let config = ServerConfig::default();
		assert!(should_skip_pow(&config, true, true));
		assert!(!should_skip_pow(&config, false, true));
	}

	#[test]
	fn mainnet_ignores_disable_checkpoints() {
		let mut config = ServerConfig::default();
		config.disable_checkpoints = Some(true);
		assert!(should_skip_pow(&config, true, true));
		assert!(!should_skip_pow(&config, false, true));

		config.chain_type = global::ChainTypes::AutomatedTesting;
		assert!(should_skip_pow(&config, false, true));
	}

	#[test]
	fn only_peer_attributable_txhashset_errors_are_bannable() {
		assert!(is_bad_txhashset_data(&chain::Error::InvalidTxHashSet(
			"invalid archive".to_owned()
		)));
		assert!(!is_bad_txhashset_data(&chain::Error::Io(
			std::io::Error::new(std::io::ErrorKind::Other, "disk failure")
		)));
	}
}
