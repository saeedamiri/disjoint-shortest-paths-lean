/-
Soundness, completeness and correctness of the table (lem:sound, lem:complete, cor:correct).

Paper: "Directed k Disjoint Shortest Paths Is Polynomial for Every Fixed k" (Saeed Amiri),
Section "The algorithm", subsection "Correctness".
-/
import DSPP.Leaf
import DSPP.HierarchyThm

open Classical

namespace DSPP

variable {k : ℕ} [NeZero k] {V : Type*} [Fintype V] [DecidableEq V]

namespace Instance

variable (G : Instance V k)

/-- lem:sound.  `T(U, Π)` implies `S(U, Π)` (stated for every `U` and every `Π` with ends in
`U`, in particular for every entry). -/
theorem lem_sound (U : Finset V) (Dm : Finset (Demand V k))
    (hends : ∀ δ ∈ Dm, δ.2.1 ∈ U ∧ δ.2.2 ∈ U) (h : G.Tab U Dm) : G.Sem U Dm := by
  sorry

/-- lem:complete.  If the instance has a solution, then `T(V, Π_0)` is true. -/
theorem lem_complete (h : G.HasSolution) : G.Tab Finset.univ G.Pi0 := by
  sorry

/-- cor:correct.  `T(V, Π_0)` is true if and only if the instance has a solution. -/
theorem cor_correct : G.Tab Finset.univ G.Pi0 ↔ G.HasSolution := by
  sorry

/-- The root `(V, Π_0)` is an entry of the table (`|Π_0| = k ≤ P(k)`). -/
theorem isEntry_root : G.IsEntry Finset.univ G.Pi0 := by
  sorry

end Instance

end DSPP
