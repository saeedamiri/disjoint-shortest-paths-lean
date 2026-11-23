/-
Soundness, completeness and correctness of the table (lem:sound, lem:complete, cor:correct).

Paper: "Directed k Disjoint Shortest Paths Is Polynomial for Every Fixed k" (Saeed Amiri),
Section "The algorithm", subsection "Correctness".
-/
import DSPP.Correctness.Sound
import DSPP.Correctness.Complete

open Classical

namespace DSPP

variable {k : ℕ} [NeZero k] {V : Type*} [Fintype V] [DecidableEq V]

namespace Instance

variable (G : Instance V k)

/-- lem:sound.  `T(U, Π)` implies `S(U, Π)` (stated for every `U` and every `Π` with ends in
`U`, in particular for every entry). -/
theorem lem_sound (U : Finset V) (Dm : Finset (Demand V k))
    (hends : ∀ δ ∈ Dm, δ.2.1 ∈ U ∧ δ.2.2 ∈ U) (h : G.Tab U Dm) : G.Sem U Dm :=
  G.sound_aux _ U Dm rfl hends h

/-- lem:complete.  If the instance has a solution, then `T(V, Π_0)` is true. -/
theorem lem_complete (h : G.HasSolution) : G.Tab Finset.univ G.Pi0 :=
  G.complete_aux h

/-- cor:correct.  `T(V, Π_0)` is true if and only if the instance has a solution. -/
theorem cor_correct : G.Tab Finset.univ G.Pi0 ↔ G.HasSolution :=
  ⟨fun h => G.sem_root_iff.1
    (G.lem_sound _ _ (fun _ _ => ⟨Finset.mem_univ _, Finset.mem_univ _⟩) h), G.lem_complete⟩

/-- The root `(V, Π_0)` is an entry of the table (`|Π_0| = k ≤ P(k)`). -/
theorem isEntry_root : G.IsEntry Finset.univ G.Pi0 := by
  refine ⟨G.lem_box_a.2, ?_, fun _ _ => ⟨Finset.mem_univ _, Finset.mem_univ _⟩⟩
  refine (Finset.card_image_le.trans (by simp)).trans (Nat.le_add_left k _)

end Instance

end DSPP
