/-
Termination of the construction (lem:termination).

Paper: "Directed k Disjoint Shortest Paths Is Polynomial for Every Fixed k" (Saeed Amiri),
Section "The cut hierarchy", subsection "Construction and termination".
-/
import DSPP.Averaging

open Classical

namespace DSPP

variable {k : ℕ} [NeZero k] {V : Type*} [Fintype V] [DecidableEq V]

namespace Instance

variable (G : Instance V k)

/-- lem:termination.  The construction terminates: there is no infinite sequence of cells,
each a child of the previous one under a step of def:construction, whatever good levels are
chosen. -/
theorem lem_termination (Rs : Fin k → List V) :
    WellFounded (fun C' C : Cell k => G.ConstrStep Rs C' C) := by
  sorry

/-- A cell whose vertex set meets two point classes has positive width (text of
def:construction). -/
theorem width_pos_of_not_atMostOneClass (C : Cell k)
    (hC : ¬ G.AtMostOneClass (G.cellVerts C)) : 0 < C.width := by
  sorry

/-- A cell that is not a leaf of the construction can be cut: it has positive width and a good
level in a widest star coordinate (cor:goodlevel; text of def:construction). -/
theorem exists_constrCut (Rs : Fin k → List V) (hRs : ∀ l, G.IsDPath l (Rs l)) (C : Cell k)
    (hC : ¬ G.AtMostOneClass (G.cellVerts C)) :
    ∃ j lam, G.ConstrCut Rs C j lam := by
  sorry

/-- The tree of def:construction exists (and is finite) for every start cell. -/
theorem exists_constructionTree (Rs : Fin k → List V) (hRs : ∀ l, G.IsDPath l (Rs l))
    (C : Cell k) : ∃ T : CutTree k, G.IsConstructionTree Rs T C := by
  sorry

/-- A construction tree is a hierarchy: since `θ > 0`, every chosen level lies strictly between
the bounds (text after def:construction). -/
theorem isHierarchy_of_isConstructionTree (Rs : Fin k → List V) (T : CutTree k) (C : Cell k)
    (h : G.IsConstructionTree Rs T C) : G.IsHierarchy T C := by
  induction T generalizing C with
  | leaf => trivial
  | node j lam lt rt ihl ihr =>
    obtain ⟨⟨hC, -, hg, hlo, hhi, -⟩, hl, hr⟩ := h
    have hθ : (0 : ℝ) < theta k := by
      unfold theta
      have : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne k)
      positivity
    have hw : 0 < C.width := G.width_pos_of_not_atMostOneClass C hC
    exact ⟨hg, by nlinarith, by nlinarith, ihl _ hl, ihr _ hr⟩

end Instance

end DSPP
