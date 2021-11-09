initSidebarItems({"fn":[["clean_txhashset_folder","Clean the txhashset folder"],["extending","Starts a new unit of work to extend the chain with additional blocks, accepting a closure that will work within that unit of work. The closure has access to an Extension object that allows the addition of blocks to the txhashset and the checking of the current tree roots."],["extending_readonly","Starts a new unit of work to extend (or rewind) the chain with additional blocks. Accepts a closure that will operate within that unit of work. The closure has access to an Extension object that allows the addition of blocks to the txhashset and the checking of the current tree roots."],["header_extending","Start a new header MMR unit of work. This MMR can be extended individually beyond the other (output, rangeproof and kernel) MMRs to allow headers to be validated before we receive the full block data."],["rewindable_kernel_view","Rewindable (but still readonly) view on the kernel MMR. The underlying backend is readonly. But we permit the PMMR to be “rewound” via last_pos. We create a new db batch for this view and discard it (rollback) when we are done with the view."],["txhashset_replace","Overwrite txhashset folders in “to” folder with “from” folder"],["utxo_view","Readonly view on the UTXO set. Based on the current txhashset output_pmmr."],["zip_read","Packages the txhashset data files into a zip and returns a Read to the resulting file"],["zip_write","Extract the txhashset data from a zip file and writes the content into the txhashset storage dir"]],"struct":[["BitmapAccumulator","The “bitmap accumulator” allows us to commit to a specific bitmap by splitting it into fragments and inserting these fragments into an MMR to produce an overall root hash. Leaves in the MMR are fragments of the bitmap consisting of 1024 contiguous bits from the overall bitmap. The first (leftmost) leaf in the MMR represents the first 1024 bits of the bitmap, the next leaf is the next 1024 bits of the bitmap etc."],["BitmapChunk","A bitmap “chunk” representing 1024 contiguous bits of the overall bitmap. The first 1024 bits belong in one chunk. The next 1024 bits in the next chunk, etc."],["Extension","Allows the application of new blocks on top of the txhashset in a reversible manner within a unit of work provided by the `extending` function."],["ExtensionPair","An extension “pair” consisting of a txhashet extension (outputs, rangeproofs, kernels) and the associated header extension."],["HeaderExtension","A header extension to allow the header MMR to extend beyond the other MMRs individually. This is to allow headers to be validated against the MMR before we have the full block data."],["PMMRHandle","Convenience wrapper around a single prunable MMR backend."],["RewindableKernelView","Rewindable (but readonly) view of the kernel set (based on kernel MMR)."],["TxHashSet","An easy to manipulate structure holding the 3 sum trees necessary to validate blocks and capturing the Output set, the range proofs and the kernels. Also handles the index of Commitments to positions in the output and range proof pmmr trees."],["UTXOView","Readonly view of the UTXO set (based on output MMR)."]]});