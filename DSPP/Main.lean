/-
The main theorem (thm:main) in the form of this formalization.

Paper: "Directed k Disjoint Shortest Paths Is Polynomial for Every Fixed k" (Saeed Amiri),
Theorem "Main theorem" (thm:main), proved at the end of Section "The algorithm".

The algorithm of the paper answers the root entry `T(V, Π_0)` of the guillotine table
(`Instance.Tab`, def:table).  The theorem below states
1. correctness: the root entry is true iff the instance has `k` pairwise vertex-disjoint
   shortest `s_i`--`t_i` paths (cor:correct);
2. complexity: the work of the table computation, counted as (entry, split, interface) triples
   plus pebble-game graph sizes, is at most `f(k) · n^{6k^2-4k-1}` (lem:time).
-/
import DSPP.Correctness
import DSPP.Complexity

namespace DSPP

/-- thm:main.  Correctness and the `n^{6k^2-4k-1}` bound of the guillotine table. -/
theorem thm_main :
    (∀ (k : ℕ) [NeZero k] (V : Type) [Fintype V] [DecidableEq V] (G : Instance V k),
      G.Tab Finset.univ G.Pi0 ↔ G.HasSolution) ∧
    ∃ f : ℕ → ℕ, ∀ (k : ℕ) [NeZero k] (V : Type) [Fintype V] [DecidableEq V]
      (G : Instance V k),
      G.splitWork + G.leafWork ≤ f k * Fintype.card V ^ (6 * k ^ 2 - 4 * k - 1) :=
  ⟨fun _ _ _ _ _ G => G.cor_correct, lem_time⟩

end DSPP
