# Directed k Disjoint Shortest Paths in Lean 4

A Lean 4 / Mathlib formalization of the paper *Directed k Disjoint Shortest Paths Is
Polynomial for Every Fixed k* (Saeed Amiri).

The main theorem, `DSPP.thm_main` in `DSPP/Main.lean`, states two things:

- **Correctness.** The guillotine table defined in `DSPP/Table.lean` accepts at its root exactly
  when the instance has k pairwise vertex-disjoint shortest paths.
- **Size.** The work of the table, counted over its entries, splits and interfaces, is at most
  `f(k) · n^(6k²-4k-1)`. The recursion from the root visits only entries, so this covers the
  evaluation of the root.

`DSPP/Examples.lean` gives an explicit instance, showing the hypotheses are satisfiable.

**Status:** `DSPP.thm_main` and `DSPP.cor_undirected` are fully proved: `#print axioms` lists
only `propext`, `Classical.choice` and `Quot.sound`, and the library contains no `sorry`. Each Lean
theorem is named after its label in the paper, which its docstring also gives.
`DEVIATIONS.md` records where a Lean statement differs in form from the paper.

## Building

Requires `elan`. Then run:

```
lake exe cache get
lake build
```

Toolchain: Lean 4.36.0, Mathlib v4.36.0.
