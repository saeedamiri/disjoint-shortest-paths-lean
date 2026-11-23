/-
Few pieces in every cell (lem:pieces).

Paper: "Directed k Disjoint Shortest Paths Is Polynomial for Every Fixed k" (Saeed Amiri),
Section "The cut hierarchy", subsection "Few pieces".
-/
import DSPP.Hierarchy

open Classical

namespace DSPP

variable {k : ℕ} [NeZero k] {V : Type*} [Fintype V] [DecidableEq V]

namespace Instance

variable (G : Instance V k)

/-- lem:pieces, pieces part, stated for every hierarchy whose root contains all vertex points
and whose cuts are crossed at most `3k - 4` times (these are the only facts the paper's charging
argument uses; the tree of def:construction has them).  Every cell of the hierarchy contains at
most `P(k)` pieces of `R_1, ..., R_k` in total.  See `DEVIATIONS.md` for the omitted count of
components of `γ_l⁻¹(C)`. -/
theorem lem_pieces (Rs : Fin k → List V) (C0 : Cell k) (T : CutTree k)
    (hT : G.IsHierarchy T C0) (hroot : ∀ v, G.pt v ∈ C0.carrier)
    (hcut : ∀ C j lam, (C, some (j, lam)) ∈ T.nodes C0 → G.crossNum Rs C j lam ≤ 3 * k - 4) :
    ∀ C o, (C, o) ∈ T.nodes C0 → numPieces Rs (G.cellVerts C) ≤ P k := by
  sorry

end Instance

end DSPP
