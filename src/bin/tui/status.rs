// Copyright 2020 The Epic Developers
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

//! Basic status view definition

use chrono::prelude::Utc;
use cursive::direction::Orientation;
use cursive::view::{Nameable, View};
use cursive::views::{LinearLayout, ResizedView, TextView};
use cursive::Cursive;

use crate::tui::constants::VIEW_BASIC_STATUS;
use crate::tui::types::TUIStatusListener;

use crate::chain::SyncStatus;
use crate::core::pow::PoWType;
use crate::servers::ServerStats;

const NANO_TO_MILLIS: f64 = 1.0 / 1_000_000.0;

pub struct TUIStatusView;

impl TUIStatusView {
	fn update_sync_status(sync_status: SyncStatus) -> String {
		match sync_status {
			SyncStatus::Initial => "Initializing".to_string(),
			SyncStatus::NoSync => "Running".to_string(),
			SyncStatus::AwaitingPeers(_) => "Waiting for peers".to_string(),
			SyncStatus::HeaderSync {
				current_height,
				highest_height,
			} => {
				let percent = if highest_height == 0 {
					0
				} else {
					current_height * 100 / highest_height
				};
				format!("Sync step 1/7: Downloading headers: {}%", percent)
			}
			SyncStatus::TxHashsetDownload {
				start_time,
				prev_update_time,
				update_time: _,
				prev_downloaded_size,
				downloaded_size,
				total_size,
			} => {
				if total_size > 0 {
					let percent = if total_size > 0 {
						downloaded_size * 100 / total_size
					} else {
						0
					};
					let start = prev_update_time.timestamp_nanos_opt().unwrap();
					let fin = Utc::now().timestamp_nanos_opt().unwrap();
					let dur_ms = (fin - start) as f64 * NANO_TO_MILLIS;

					format!("Sync step 2/7: Downloading {}(MB) chain state for state sync: {}% at {:.1?}(kB/s)",
							total_size / 1_000_000,
							percent,
							if dur_ms > 1.0f64 { (downloaded_size - prev_downloaded_size) as f64 / dur_ms as f64 } else { 0f64 },
					)
				} else {
					let start = start_time.timestamp_millis();
					let fin = Utc::now().timestamp_millis();
					let dur_secs = (fin - start) / 1000;

					format!("Sync step 2/7: Downloading chain state for state sync. Waiting remote peer to start: {}s",
							dur_secs,
					)
				}
			}
			SyncStatus::TxHashsetSetup => {
				"Sync step 3/7: Preparing chain state for validation".to_string()
			}
			SyncStatus::TxHashsetRangeProofsValidation {
				rproofs,
				rproofs_total,
			} => {
				let r_percent = if rproofs_total > 0 {
					(rproofs * 100) / rproofs_total
				} else {
					0
				};
				format!(
					"Sync step 4/7: Validating chain state - range proofs: {}%",
					r_percent
				)
			}
			SyncStatus::TxHashsetKernelsValidation {
				kernels,
				kernels_total,
			} => {
				let k_percent = if kernels_total > 0 {
					(kernels * 100) / kernels_total
				} else {
					0
				};
				format!(
					"Sync step 5/7: Validating chain state - kernels: {}%",
					k_percent
				)
			}
			SyncStatus::TxHashsetSave => {
				"Sync step 6/7: Finalizing chain state for state sync".to_string()
			}
			SyncStatus::TxHashsetDone => {
				"Sync step 6/7: Finalized chain state for state sync".to_string()
			}
			SyncStatus::BodySync {
				current_height,
				highest_height,
			} => {
				let percent = if highest_height == 0 {
					0
				} else {
					current_height * 100 / highest_height
				};
				format!("Sync step 7/7: Downloading blocks: {}%", percent)
			}
			SyncStatus::Shutdown => "Shutting down, closing connections".to_string(),
		}
	}
}

impl TUIStatusListener for TUIStatusView {
	/// Create basic status view
	fn create() -> Box<dyn View> {
		let basic_status_view = ResizedView::with_full_screen(
			LinearLayout::new(Orientation::Vertical)
				.child(
					LinearLayout::new(Orientation::Horizontal)
						.child(TextView::new("Current Status:               "))
						.child(TextView::new("Starting").with_name("basic_current_status")),
				)
				.child(
					LinearLayout::new(Orientation::Horizontal)
						.child(TextView::new("Connected Peers:              "))
						.child(TextView::new("0").with_name("connected_peers")),
				)
				.child(
					LinearLayout::new(Orientation::Horizontal)
						.child(TextView::new("Disk Usage (GB):              "))
						.child(TextView::new("0").with_name("disk_usage")),
				)
				.child(
					LinearLayout::new(Orientation::Horizontal).child(TextView::new(
						"--------------------------------------------------------",
					)),
				)
				.child(
					LinearLayout::new(Orientation::Horizontal)
						.child(TextView::new("Header Tip Hash:              "))
						.child(TextView::new("  ").with_name("basic_header_tip_hash")),
				)
				.child(
					LinearLayout::new(Orientation::Horizontal)
						.child(TextView::new("Header Chain Height:          "))
						.child(TextView::new("  ").with_name("basic_header_chain_height")),
				)
				.child(
					LinearLayout::new(Orientation::Horizontal)
						.child(TextView::new("Header Cumulative Difficulty: "))
						.child(TextView::new("  ").with_name("basic_header_total_difficulty")),
				)
				.child(
					LinearLayout::new(Orientation::Horizontal)
						.child(TextView::new("Header Tip Timestamp:         "))
						.child(TextView::new("  ").with_name("basic_header_timestamp")),
				)
				.child(
					LinearLayout::new(Orientation::Horizontal).child(TextView::new(
						"--------------------------------------------------------",
					)),
				)
				.child(
					LinearLayout::new(Orientation::Horizontal)
						.child(TextView::new("Chain Tip Hash:               "))
						.child(TextView::new("  ").with_name("tip_hash")),
				)
				.child(
					LinearLayout::new(Orientation::Horizontal)
						.child(TextView::new("Chain Height:                 "))
						.child(TextView::new("  ").with_name("chain_height")),
				)
				.child(
					LinearLayout::new(Orientation::Horizontal)
						.child(TextView::new("Chain Cumulative Difficulty:  "))
						.child(TextView::new("  ").with_name("basic_total_difficulty")),
				)
				.child(
					LinearLayout::new(Orientation::Horizontal)
						.child(TextView::new("Chain Tip Timestamp:          "))
						.child(TextView::new("  ").with_name("chain_timestamp")),
				)
				.child(
					LinearLayout::new(Orientation::Horizontal).child(TextView::new(
						"--------------------------------------------------------",
					)),
				)
				.child(
					LinearLayout::new(Orientation::Horizontal)
						.child(TextView::new("Transaction Pool Size:        "))
						.child(TextView::new("0").with_name("tx_pool_size"))
						.child(TextView::new(" ("))
						.child(TextView::new("0").with_name("tx_pool_kernels"))
						.child(TextView::new(")")),
				)
				.child(
					LinearLayout::new(Orientation::Horizontal)
						.child(TextView::new("Stem Pool Size:               "))
						.child(TextView::new("0").with_name("stem_pool_size"))
						.child(TextView::new(" ("))
						.child(TextView::new("0").with_name("stem_pool_kernels"))
						.child(TextView::new(")")),
				)
				.child(
					LinearLayout::new(Orientation::Horizontal).child(TextView::new(
						"--------------------------------------------------------",
					)),
				)
				.child(
					LinearLayout::new(Orientation::Horizontal)
						.child(TextView::new("  ").with_name("basic_mining_config_status")),
				)
				.child(
					LinearLayout::new(Orientation::Horizontal)
						.child(TextView::new("  ").with_name("basic_mining_status")),
				)
				.child(
					LinearLayout::new(Orientation::Horizontal)
						.child(TextView::new("  ").with_name("basic_network_info")),
				), //.child(logo_view)
		);
		Box::new(basic_status_view.with_name(VIEW_BASIC_STATUS))
	}

	fn update(c: &mut Cursive, stats: &ServerStats) {
		let basic_status = TUIStatusView::update_sync_status(stats.sync_status);

		let cuckoo_diff = stats.chain_stats.total_difficulty.to_num(PoWType::Cuckatoo);
		let progpow_diff = stats.chain_stats.total_difficulty.to_num(PoWType::ProgPow);
		let randomx_diff = stats.chain_stats.total_difficulty.to_num(PoWType::RandomX);

		let head_total_difficulty = format!(
			"Cuckatoo: {}, ProgPow: {}, RandomX: {}",
			cuckoo_diff, progpow_diff, randomx_diff,
		);

		c.call_on_name("basic_current_status", |t: &mut TextView| {
			t.set_content(basic_status);
		});
		c.call_on_name("connected_peers", |t: &mut TextView| {
			t.set_content(stats.peer_count.to_string());
		});
		c.call_on_name("disk_usage", |t: &mut TextView| {
			t.set_content(stats.disk_usage_gb.clone());
		});
		c.call_on_name("tip_hash", |t: &mut TextView| {
			t.set_content(stats.chain_stats.last_block_h.to_string() + "...");
		});
		c.call_on_name("chain_height", |t: &mut TextView| {
			t.set_content(stats.chain_stats.height.to_string());
		});
		c.call_on_name("basic_total_difficulty", |t: &mut TextView| {
			t.set_content(head_total_difficulty);
		});
		c.call_on_name("chain_timestamp", |t: &mut TextView| {
			t.set_content(stats.chain_stats.latest_timestamp.to_string());
		});

		let cuckoo_header_diff = stats
			.header_stats
			.total_difficulty
			.to_num(PoWType::Cuckatoo);
		let progpow_header_diff = stats.header_stats.total_difficulty.to_num(PoWType::ProgPow);
		let randomx_header_diff = stats.header_stats.total_difficulty.to_num(PoWType::RandomX);

		let header_total_difficulty = format!(
			"Cuckatoo: {}, ProgPow: {}, RandomX: {}",
			cuckoo_header_diff, progpow_header_diff, randomx_header_diff,
		);

		c.call_on_name("basic_header_tip_hash", |t: &mut TextView| {
			t.set_content(stats.header_stats.last_block_h.to_string() + "...");
		});
		c.call_on_name("basic_header_chain_height", |t: &mut TextView| {
			t.set_content(stats.header_stats.height.to_string());
		});
		c.call_on_name("basic_header_total_difficulty", |t: &mut TextView| {
			t.set_content(header_total_difficulty);
		});
		c.call_on_name("basic_header_timestamp", |t: &mut TextView| {
			t.set_content(stats.header_stats.latest_timestamp.to_string());
		});

		if let Some(tx_stats) = &stats.tx_stats {
			c.call_on_name("tx_pool_size", |t: &mut TextView| {
				t.set_content(tx_stats.tx_pool_size.to_string());
			});
			c.call_on_name("stem_pool_size", |t: &mut TextView| {
				t.set_content(tx_stats.stem_pool_size.to_string());
			});
			c.call_on_name("tx_pool_kernels", |t: &mut TextView| {
				t.set_content(tx_stats.tx_pool_kernels.to_string());
			});
			c.call_on_name("stem_pool_kernels", |t: &mut TextView| {
				t.set_content(tx_stats.stem_pool_kernels.to_string());
			});
		}
	}
}

#[test]
fn test_status_txhashset_kernels() {
	let status = SyncStatus::TxHashsetKernelsValidation {
		kernels: 201,
		kernels_total: 5000,
	};
	let basic_status = TUIStatusView::update_sync_status(status);
	assert!(basic_status.contains("4%"), basic_status);
}

#[test]
fn test_status_txhashset_rproofs() {
	let status = SyncStatus::TxHashsetRangeProofsValidation {
		rproofs: 643,
		rproofs_total: 1000,
	};
	let basic_status = TUIStatusView::update_sync_status(status);
	assert!(basic_status.contains("64%"), basic_status);
}
