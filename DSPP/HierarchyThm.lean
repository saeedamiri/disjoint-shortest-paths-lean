/-
The cut hierarchy theorem (thm:hierarchy) and cor:crossarcs.

Paper: "Directed k Disjoint Shortest Paths Is Polynomial for Every Fixed k" (Saeed Amiri),
Section "The cut hierarchy".
-/
import DSPP.Termination
import DSPP.Pieces

open Classical

namespace DSPP

variable {k : ℕ} [NeZero k] {V : Type*} [Fintype V] [DecidableEq V]

namespace Instance

variable (G : Instance V k)

/-- thm:hierarchy.  For every `k`-tuple of `D_l`-paths there is a hierarchy such that
(H1) the root cell contains every vertex point;
(H2) every cut `(1, j, λ)` of a cell `C` has `N_C(λ) ≤ 3k - 4`;
(H3) every cell contains at most `P(k)` pieces of the paths in total;
(H4) a cell is a leaf iff `V(C)` meets at most one point class. -/
theorem thm_hierarchy (Rs : Fin k → List V) (hRs : ∀ l, G.IsDPath l (Rs l)) :
    ∃ (C0 : Cell k) (T : CutTree k), G.IsHierarchy T C0 ∧
      (∀ v, G.pt v ∈ C0.carrier) ∧
      (∀ C j lam, (C, some (j, lam)) ∈ T.nodes C0 → G.crossNum Rs C j lam ≤ 3 * k - 4) ∧
      (∀ C o, (C, o) ∈ T.nodes C0 → numPieces Rs (G.cellVerts C) ≤ P k) ∧
      (∀ C o, (C, o) ∈ T.nodes C0 → (o = none ↔ G.AtMostOneClass (G.cellVerts C))) := by
  sorry

/-- The arcs with one end on each side of a cut of `C` at a generic level `λ`, with
`a_j < λ < b_j`, are counted by `N_C(λ)` (proof of cor:crossarcs). -/
theorem crossArcCount_le_crossNum (Rs : Fin k → List V) (C : Cell k) (j : StarIdx k) (lam : ℝ)
    (hg : G.IsGeneric j lam) (hlo : C.lo j < lam) (hhi : lam < C.hi j) :
    G.crossArcCount Rs C j lam ≤ G.crossNum Rs C j lam := by
  sorry

/-- cor:crossarcs.  In a hierarchy with (H2), if `C` is cut into `C⁻` and `C⁺`, then at most
`3k - 4` arcs of `R_1, ..., R_k` (counted with multiplicity over the paths) have one end in
`V(C⁻)` and the other in `V(C⁺)`. -/
theorem cor_crossarcs (Rs : Fin k → List V) (C0 : Cell k) (T : CutTree k)
    (hT : G.IsHierarchy T C0)
    (hcut : ∀ C j lam, (C, some (j, lam)) ∈ T.nodes C0 → G.crossNum Rs C j lam ≤ 3 * k - 4)
    (C : Cell k) (j : StarIdx k) (lam : ℝ) (hC : (C, some (j, lam)) ∈ T.nodes C0) :
    G.crossArcCount Rs C j lam ≤ 3 * k - 4 := by
  obtain ⟨hg, hlo, hhi⟩ := G.cut_of_mem_nodes T C0 hT hC
  exact (G.crossArcCount_le_crossNum Rs C j lam hg hlo hhi).trans (hcut C j lam hC)

end Instance

end DSPP
