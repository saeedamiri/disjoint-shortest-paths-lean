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

/-- Every cut of a construction tree is a step of def:construction. -/
theorem hier_constrCut_of_mem_nodes (Rs : Fin k → List V) (T : CutTree k) (C0 : Cell k)
    (hT : G.IsConstructionTree Rs T C0) :
    ∀ C j lam, (C, some (j, lam)) ∈ T.nodes C0 → G.ConstrCut Rs C j lam := by
  induction T generalizing C0 with
  | leaf => intro C j lam hC; simp [CutTree.nodes] at hC
  | node j' lam' lt rt ihl ihr =>
    intro C j lam hC
    simp only [CutTree.nodes, List.mem_cons, List.mem_append, Prod.mk.injEq,
      Option.some.injEq] at hC
    rcases hC with ⟨rfl, rfl, rfl⟩ | hC | hC
    · exact hT.1
    · exact ihl _ hT.2.1 C j lam hC
    · exact ihr _ hT.2.2 C j lam hC

/-- In a construction tree, a cell is a leaf iff its vertex set meets at most one point
class. -/
theorem hier_leaf_iff_of_mem_nodes (Rs : Fin k → List V) (T : CutTree k) (C0 : Cell k)
    (hT : G.IsConstructionTree Rs T C0) :
    ∀ C o, (C, o) ∈ T.nodes C0 → (o = none ↔ G.AtMostOneClass (G.cellVerts C)) := by
  induction T generalizing C0 with
  | leaf =>
    intro C o hC
    simp only [CutTree.nodes, List.mem_singleton, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl⟩ := hC
    exact ⟨fun _ => hT, fun _ => rfl⟩
  | node j lam lt rt ihl ihr =>
    intro C o hC
    simp only [CutTree.nodes, List.mem_cons, List.mem_append, Prod.mk.injEq] at hC
    rcases hC with ⟨rfl, rfl⟩ | hC | hC
    · exact ⟨fun h => absurd h (by simp), fun h => absurd h hT.1.1⟩
    · exact ihl _ hT.2.1 C o hC
    · exact ihr _ hT.2.2 C o hC

/-- The root cell contains every vertex point. -/
theorem hier_pt_mem_rootCell (v : V) : G.pt v ∈ G.rootCell.carrier := fun j =>
  ⟨Finset.inf'_le (G.starX j) (Finset.mem_univ v),
    Finset.le_sup' (G.starX j) (Finset.mem_univ v)⟩

/-- An arc from `C⁻` to `C⁺` of a cut at a generic level strictly inside the bounds crosses the
level at a point of `C`. -/
theorem hier_segCross_of_lower_upper (C : Cell k) (j : StarIdx k) (lam : ℝ) (hlo : C.lo j < lam)
    (hhi : lam < C.hi j) {p q : Fin k → ℝ} (hp : p ∈ (C.lower j lam).carrier)
    (hq : q ∈ (C.upper j lam).carrier) (hpg : X 0 j.1 p ≠ lam) (hqg : X 0 j.1 q ≠ lam) :
    segCross C j lam p q := by
  have hp' : X 0 j.1 p < lam := by
    have := (hp j).2
    simp only [Cell.lower, Function.update_self, max_eq_right hlo.le] at this
    exact lt_of_le_of_ne this hpg
  have hq' : lam < X 0 j.1 q := by
    have := (hq j).1
    simp only [Cell.upper, Function.update_self, min_eq_right hhi.le] at this
    exact lt_of_le_of_ne this hqg.symm
  refine ⟨Or.inl ⟨hp', hq'⟩, ?_⟩
  have hd : 0 < X 0 j.1 q - X 0 j.1 p := by linarith
  exact PiecesProof.segment_mem C (PiecesProof.lower_carrier_subset C j lam hhi.le hp)
    (PiecesProof.upper_carrier_subset C j lam hlo.le hq) (div_nonneg (by linarith) hd.le)
    ((div_le_one hd).2 (by linarith))

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
  obtain ⟨T, hT⟩ := G.exists_constructionTree Rs hRs G.rootCell
  have hH := G.isHierarchy_of_isConstructionTree Rs T _ hT
  have hcut : ∀ C j lam, (C, some (j, lam)) ∈ T.nodes G.rootCell →
      G.crossNum Rs C j lam ≤ 3 * k - 4 := fun C j lam h =>
    (G.hier_constrCut_of_mem_nodes Rs T _ hT C j lam h).2.2.2.2.2
  exact ⟨G.rootCell, T, hH, G.hier_pt_mem_rootCell, hcut,
    G.lem_pieces Rs _ T hH G.hier_pt_mem_rootCell hcut, G.hier_leaf_iff_of_mem_nodes Rs T _ hT⟩

/-- The arcs with one end on each side of a cut of `C` at a generic level `λ`, with
`a_j < λ < b_j`, are counted by `N_C(λ)` (proof of cor:crossarcs). -/
theorem crossArcCount_le_crossNum (Rs : Fin k → List V) (C : Cell k) (j : StarIdx k) (lam : ℝ)
    (hg : G.IsGeneric j lam) (hlo : C.lo j < lam) (hhi : lam < C.hi j) :
    G.crossArcCount Rs C j lam ≤ G.crossNum Rs C j lam := by
  unfold crossArcCount crossNum
  apply Finset.sum_le_sum
  intro l _
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  apply List.countP_mono_left
  intro e _ he
  simp only [decide_eq_true_eq] at he ⊢
  simp only [cellVerts, Finset.mem_filter, Finset.mem_univ, true_and] at he
  rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact hier_segCross_of_lower_upper C j lam hlo hhi h1 h2 (hg e.1) (hg e.2)
  · exact PiecesProof.segCross_comm _ _ _ _ _
      (hier_segCross_of_lower_upper C j lam hlo hhi h2 h1 (hg e.2) (hg e.1))

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
