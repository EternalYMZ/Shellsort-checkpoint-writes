# Minimum writes between prescribed checkpoints

Going from [2,0,1] to [0,1,2] requires three whole-record writes to the main array. All three slots change, and a read-only source of the target records suffices to write each once.

For checkpoints $A_0,\ldots,A_p$ with the same distinct keys, the exact minimum is
$$\sum_{t=1}^p\#\{i:A_{t-1}[i]\ne A_t[i]\}.$$
A slot left unwritten between two checkpoints retains its old content. Conversely, write the target record once into each changed slot. Concatenating these constructions reaches every checkpoint, including when a slot later returns to its initial value.

Lean verifies the write trace, lower bound and attaining construction for accessible target records. This cost counts main-array writes. Computing the ranks, producing target records and using auxiliary storage have separate costs. The analytical extensions concerning cycle rotation with one temporary record and average total time for dense gap tables are outside this formal statement.

[PhysicalSlotWrites.lean](https://github.com/EternalYMZ/Shellsort-checkpoint-writes/blob/7920dab6af0fbe89b72d2389582556253a89189f/Shellsort/PhysicalSlotWrites.lean) · [CheckpointChange.lean](https://github.com/EternalYMZ/Shellsort-checkpoint-writes/blob/7920dab6af0fbe89b72d2389582556253a89189f/Shellsort/CheckpointChange.lean)
