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
  sorry

end Instance

end DSPP
