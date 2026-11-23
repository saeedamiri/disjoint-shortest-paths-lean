/-
Box sets (def:box, lem:box) and point classes as vertex sets.

Paper: "Directed k Disjoint Shortest Paths Is Polynomial for Every Fixed k" (Saeed Amiri),
Section "The algorithm", subsection "Box sets".
-/
import DSPP.Hierarchy

open Classical

namespace DSPP

variable {k : ℕ} [NeZero k] {V : Type*} [Fintype V] [DecidableEq V]

namespace Instance

variable (G : Instance V k)

/-- `Λ_j = {X_{1j}(v) : v ∈ V}`. -/
noncomputable def Lam (j : StarIdx k) : Finset ℝ := Finset.univ.image (G.starX j)

/-- The vertices with `α_j ≤ X_{1j}(v) ≤ β_j` for all star indices `j`. -/
noncomputable def boxOf (α β : StarIdx k → ℝ) : Finset V :=
  Finset.univ.filter fun v => ∀ j, α j ≤ G.starX j v ∧ G.starX j v ≤ β j

/-- def:box.  A box set: a non-empty set `{v : α_j ≤ X_{1j}(v) ≤ β_j}` with `α_j, β_j ∈ Λ_j`. -/
def IsBoxSet (U : Finset V) : Prop :=
  U.Nonempty ∧ ∃ α β : StarIdx k → ℝ, (∀ j, α j ∈ G.Lam j ∧ β j ∈ G.Lam j) ∧ U = G.boxOf α β

/-- def:box.  The family `𝒰` of box sets. -/
noncomputable def boxSets : Finset (Finset V) := Finset.univ.filter G.IsBoxSet

/-- The point class of `v`, as a set of vertices. -/
noncomputable def pointClass (v : V) : Finset V := Finset.univ.filter (G.SameClass v)

/-- `U` is a point class. -/
def IsPointClass (U : Finset V) : Prop := ∃ v, U = G.pointClass v

/-- lem:box (a).  `|𝒰| ≤ n^{2(k-1)}`, and `V ∈ 𝒰`. -/
theorem lem_box_a :
    G.boxSets.card ≤ Fintype.card V ^ (2 * (k - 1)) ∧ Finset.univ ∈ G.boxSets := by
  sorry

/-- lem:box (b).  A box set is the box set of its tight bounds. -/
theorem lem_box_b {U : Finset V} (hU : G.IsBoxSet U) (α β : StarIdx k → ℝ)
    (hα : ∀ j, IsLeast (G.starX j '' U) (α j)) (hβ : ∀ j, IsGreatest (G.starX j '' U) (β j)) :
    U = G.boxOf α β := by
  sorry

/-- lem:box (c).  If `V(C) ≠ ∅` for a cell `C`, then `V(C)` is a box set. -/
theorem lem_box_c (C : Cell k) (hC : (G.cellVerts C).Nonempty) : G.IsBoxSet (G.cellVerts C) := by
  sorry

/-- lem:box (d).  Cutting a box set at a value of `Λ_j` gives box sets (when non-empty). -/
theorem lem_box_d {U : Finset V} (hU : G.IsBoxSet U) (j : StarIdx k) {α : ℝ}
    (hα : α ∈ G.Lam j) :
    ((U.filter fun v => G.starX j v ≤ α).Nonempty →
        G.IsBoxSet (U.filter fun v => G.starX j v ≤ α)) ∧
      ((U.filter fun v => α ≤ G.starX j v).Nonempty →
        G.IsBoxSet (U.filter fun v => α ≤ G.starX j v)) := by
  sorry

/-- lem:box (e).  Every box set is a union of point classes, and a box set that meets only one
point class is that point class. -/
theorem lem_box_e {U : Finset V} (hU : G.IsBoxSet U) :
    (∀ u ∈ U, ∀ v, G.SameClass u v → v ∈ U) ∧ (G.AtMostOneClass U → G.IsPointClass U) := by
  sorry

end Instance

end DSPP
