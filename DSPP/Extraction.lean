/-
Output of a solution: the paths are read off the table.

Paper: "Directed k Disjoint Shortest Paths Is Polynomial for Every Fixed k" (Saeed Amiri),
Section "The algorithm" (the table and the proof of lem:sound).

The paper decides the problem with the table and notes that a solution is found by the usual
back-tracking through the table.  Here the paths are built from the table's own witness data,
by recursion on `|U|` along the proof of lem:sound:
* at a split entry, a split and a valid interface whose two sub-entries are true are chosen,
  the paths of the two sub-entries are built, and they are joined along the chains of the
  interface (`joinPaths`);
* at a leaf, a winning play of the pebble game is chosen, and the paths are the trajectories of
  the pebbles (`leafPaths`).
No step chooses from the existence of a solution.  `extract_isSolution` proves that the paths
form a solution whenever the root entry is true.
-/
import DSPP.Correctness

open Classical

namespace DSPP

variable {k : ℕ} [NeZero k] {V : Type*} [Fintype V] [DecidableEq V]

namespace Instance

variable (G : Instance V k)

/-- A witness of the split rule for the entry `(U, Π)`: a split `w.1` of `U` and a valid
interface `w.2` whose two sub-entries are true. -/
def SplitWit (U : Finset V) (Dm : Finset (Demand V k))
    (w : (StarIdx k × ℝ × ℝ) × Finset (ArcDemand V k)) : Prop :=
  w.1 ∈ G.splits U ∧ w.2 ∈ G.interfaces U Dm w.1 ∧ G.Valid U Dm w.1 w.2 ∧
    G.Tab (G.Uminus U w.1) (G.PiMinus U Dm w.1 w.2) ∧
    G.Tab (G.Uplus U w.1) (G.PiPlus U Dm w.1 w.2)

theorem tab_iff_splitWit {U : Finset V} {Dm : Finset (Demand V k)} (hpc : ¬ G.IsPointClass U) :
    G.Tab U Dm ↔ ∃ w, G.SplitWit U Dm w := by
  rw [Tab_eq, if_neg hpc]
  constructor
  · rintro ⟨sp, hsp, I, hI, hV, hm, hp⟩
    exact ⟨(sp, I), hsp, hI, hV, hm, hp⟩
  · rintro ⟨⟨sp, I⟩, hsp, hI, hV, hm, hp⟩
    exact ⟨sp, hsp, I, hI, hV, hm, hp⟩

/-- The paths read off the table for the entry `(U, Π)`, by recursion on `|U|`: the leaf paths
of a winning play at a point class, and otherwise the join of the paths of the two sub-entries
of a chosen split witness. -/
noncomputable def extract (U : Finset V) (Dm : Finset (Demand V k)) : Demand V k → List V :=
  if G.IsPointClass U then G.leafPaths U Dm
  else if h : ∃ w, G.SplitWit U Dm w then
    G.joinPaths U h.choose.1 h.choose.2
      (extract (G.Uminus U h.choose.1) (G.PiMinus U Dm h.choose.1 h.choose.2))
      (extract (G.Uplus U h.choose.1) (G.PiPlus U Dm h.choose.1 h.choose.2))
  else fun _ => []
termination_by U.card
decreasing_by
  · exact G.card_Uminus_lt h.choose_spec.1
  · exact G.card_Uplus_lt h.choose_spec.1

/-- The unfolding equation of `extract`. -/
theorem extract_eq (U : Finset V) (Dm : Finset (Demand V k)) :
    G.extract U Dm = if G.IsPointClass U then G.leafPaths U Dm
      else if h : ∃ w, G.SplitWit U Dm w then
        G.joinPaths U h.choose.1 h.choose.2
          (G.extract (G.Uminus U h.choose.1) (G.PiMinus U Dm h.choose.1 h.choose.2))
          (G.extract (G.Uplus U h.choose.1) (G.PiPlus U Dm h.choose.1 h.choose.2))
      else fun _ => [] := by
  rw [extract]

/-- The extracted paths witness `S(U, Π)` whenever `T(U, Π)` is true (lem:sound with explicit
paths). -/
theorem extract_semBy : ∀ (n : ℕ) (U : Finset V) (Dm : Finset (Demand V k)), U.card = n →
    (∀ δ ∈ Dm, δ.2.1 ∈ U ∧ δ.2.2 ∈ U) → G.Tab U Dm → G.SemBy U Dm (G.extract U Dm) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro U Dm hn hends h
    rw [extract_eq]
    by_cases hpc : G.IsPointClass U
    · rw [if_pos hpc]
      rw [Tab_eq, if_pos hpc] at h
      exact G.leafPaths_semBy U hpc Dm hends h.2
    · have hw : ∃ w, G.SplitWit U Dm w := (G.tab_iff_splitWit hpc).1 h
      rw [if_neg hpc, dif_pos hw]
      obtain ⟨hsp, hI, hV, hm, hp⟩ := hw.choose_spec
      exact G.sound_split_by hsp hI hV
        (ih _ (by rw [← hn]; exact G.card_Uminus_lt hsp) _ _ rfl (G.ends_PiMinus hsp hV) hm)
        (ih _ (by rw [← hn]; exact G.card_Uplus_lt hsp) _ _ rfl (G.ends_PiPlus hsp hV) hp)

/-- The solution read off the table: the path for the pair `l` is the extracted path of the
root demand `(l, s_l, t_l)`. -/
noncomputable def solution : Fin k → List V :=
  fun l => G.extract Finset.univ G.Pi0 (l, G.s l, G.t l)

/-- Output of a solution.  If the root entry `T(V, Π_0)` is true, the paths read off the table
(`solution`: chosen split witnesses at the split entries, chosen winning plays at the leaves)
form a solution. -/
theorem extract_isSolution (h : G.Tab Finset.univ G.Pi0) : G.IsSolution G.solution :=
  G.semBy_root_isSolution
    (G.extract_semBy _ _ _ rfl (fun _ _ => ⟨Finset.mem_univ _, Finset.mem_univ _⟩) h)

/-- Output of a solution, with cor:correct: the instance has a solution iff the root entry is
true, and then `solution` is one. -/
theorem solution_spec : G.HasSolution ↔ G.IsSolution G.solution :=
  ⟨fun h => G.extract_isSolution (G.cor_correct.2 h), fun h => ⟨_, h⟩⟩

end Instance

end DSPP
