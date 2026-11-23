# Directed k Disjoint Shortest Paths in Lean 4

A Lean 4 / Mathlib formalization of the paper *Directed k Disjoint Shortest Paths Is
Polynomial for Every Fixed k* (Saeed Amiri).

The main theorem, `DSPP.thm_main` in `DSPP/Main.lean`, states two things:

- **Correctness.** The guillotine table defined in `DSPP/Table.lean` accepts at its root exactly
  when the instance has k pairwise vertex-disjoint shortest paths.
- **Size.** The work of the table is at most `f(k) · n^(6k²-4k-1)`.

**Status:** work in progress. All definitions and all statements are in place. Some proofs
still use `sorry`. `PLAN.md` lists each paper label with its Lean name and status.
`DEVIATIONS.md` records where a Lean statement differs in form from the paper.

## Building

Requires `elan`. Then run:

```
lake exe cache get
lake build
```

Toolchain: Lean 4.36.0, Mathlib v4.36.0.
