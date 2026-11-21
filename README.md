# Project S · P08 · Shellsort checkpoint writes

Miaozhen Yu (俞缪臻) · [Project S directory](https://github.com/EternalYMZ/Optimal-mean-costs-of-three-pass-Shellsort/blob/main/PROJECT-S.md)

For any sequence of permutation checkpoints on the same main array, the minimum number of whole-record writes is exactly the sum of the changed-slot counts between consecutive checkpoints. Each write overwrites one named slot. The attaining trace assumes access to the target records, for example from a read-only copy. Only main-array writes are counted. Its Lean proof does not impose a single-temporary-record restriction. Other roots relate checkpoint changes to keys and gap-chain positions. The dense-prefix expectation and the worst-table running-time theorem still await formalization.

## Check the Lean statements

With Git and elan installed, run from the repository root:

```sh
lake exe cache get
lake build
```

[Shellsort.lean](Shellsort.lean) imports the included modules and prints the selected statements and their axioms. Sources and dependency revisions are pinned. Supporting modules may also occur in other paper repositories.

## Proof guide

[Read the proof idea in Chinese](brief.md). The guide explains the mathematical claim and the scope of the Lean results linked above.
