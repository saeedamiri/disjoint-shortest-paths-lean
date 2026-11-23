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

/-- cor:undirected.  The undirected problem: an undirected graph is the instance whose arc
relation and lengths are symmetric (every edge `uv` gives the arcs `(u,v)` and `(v,u)` of the
same length).  Its vertex-disjoint shortest paths are those of the symmetric directed instance,
so the guillotine table decides it within the same bound. -/
theorem cor_undirected :
    (∀ (k : ℕ) [NeZero k] (V : Type) [Fintype V] [DecidableEq V] (G : Instance V k),
      (∀ u v, G.arc u v → G.arc v u) → (∀ u v, G.len u v = G.len v u) →
      (G.Tab Finset.univ G.Pi0 ↔ G.HasSolution)) ∧
    ∃ f : ℕ → ℕ, ∀ (k : ℕ) [NeZero k] (V : Type) [Fintype V] [DecidableEq V]
      (G : Instance V k), (∀ u v, G.arc u v → G.arc v u) → (∀ u v, G.len u v = G.len v u) →
      G.splitWork + G.leafWork ≤ f k * Fintype.card V ^ (6 * k ^ 2 - 4 * k - 1) := by
  obtain ⟨hc, f, hf⟩ := thm_main
  exact ⟨fun k _ V _ _ G _ _ => hc k V G, f, fun k _ V _ _ G _ _ => hf k V G⟩

end DSPP
