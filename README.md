# Project S · P08 · Shellsort checkpoint writes

Miaozhen Yu (俞缪臻) · [Project S directory](https://github.com/EternalYMZ/Optimal-mean-costs-of-three-pass-Shellsort/blob/main/PROJECT-S.md)

The entry point checks nine bookkeeping statements for checkpoint changes. They relate changed slots to keys and tags, give a triangle inequality, and express gap-pass movement through chain position. The optimal cycle-write implementation, dense-prefix expectation and worst-table running-time theorem are outside these statements.

## Check the Lean statements

With Git and elan installed, run from the repository root:

```sh
lake exe cache get
lake build
```

[Shellsort.lean](Shellsort.lean) imports the included modules and prints the selected statements and their axioms. Sources and dependency revisions are pinned. Supporting modules may also occur in other paper repositories.
