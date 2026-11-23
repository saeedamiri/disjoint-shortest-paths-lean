/-
Hierarchies of cells (def:hierarchy) and the construction rule (def:construction).

Paper: "Directed k Disjoint Shortest Paths Is Polynomial for Every Fixed k" (Saeed Amiri),
Section "The cut hierarchy".  This file holds definitions only.
-/
import DSPP.Crossing

open Classical

namespace DSPP

/-- `P(k) = (k-1)(3k-4) + k = 3k^2 - 6k + 4`, the bound on the number of pieces in a cell. -/
def P (k : ℕ) : ℕ := (k - 1) * (3 * k - 4) + k

theorem P_eq (k : ℕ) (hk : 2 ≤ k) : P k = 3 * k ^ 2 - 6 * k + 4 := by
  sorry

/-- `θ = 1/(6k)`, the margin of the good levels (cor:goodlevel). -/
noncomputable def theta (k : ℕ) : ℝ := 1 / (6 * k)

variable {k : ℕ} [NeZero k]

/-- A finite rooted binary tree whose inner nodes carry a cut `(1, j, λ)`.  The cells are not
stored: they are determined by the root cell and the cuts (`CutTree.nodes`). -/
inductive CutTree (k : ℕ) [NeZero k] where
  | leaf : CutTree k
  | node (j : StarIdx k) (lam : ℝ) (lt rt : CutTree k) : CutTree k

namespace CutTree

/-- The nodes of the tree with root cell `C`: each node is a cell together with its cut
(`none` for a leaf).  The children of a cell `C` cut at `(1,j,λ)` are
`C⁻ = C.lower j λ` and `C⁺ = C.upper j λ`. -/
noncomputable def nodes : CutTree k → Cell k → List (Cell k × Option (StarIdx k × ℝ))
  | leaf, C => [(C, none)]
  | node j lam lt rt, C =>
      (C, some (j, lam)) :: (lt.nodes (C.lower j lam) ++ rt.nodes (C.upper j lam))

end CutTree

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The total number of pieces of `R_1, ..., R_k` in `U`. -/
def numPieces (Rs : Fin k → List V) (U : Finset V) : ℕ :=
  ∑ l : Fin k, (pieces U (Rs l)).length

namespace Instance

variable (G : Instance V k)

/-- def:hierarchy.  Every cut `(1, j, λ)` of a cell `C` has a level `λ` that is generic for
`X_{1j}` and satisfies `min_C X_{1j} < λ < max_C X_{1j}` (by lem:extent these are the bounds
`a_j < λ < b_j`). -/
def IsHierarchy : CutTree k → Cell k → Prop
  | .leaf, _ => True
  | .node j lam lt rt, C =>
      G.IsGeneric j lam ∧ C.lo j < lam ∧ lam < C.hi j ∧
        IsHierarchy lt (C.lower j lam) ∧ IsHierarchy rt (C.upper j lam)

/-- `U` meets at most one point class. -/
def AtMostOneClass (U : Finset V) : Prop := ∀ u ∈ U, ∀ v ∈ U, G.SameClass u v

/-- The number of arcs of `R_1, ..., R_k` (counted with multiplicity over the paths) with one end
in `V(C⁻)` and the other in `V(C⁺)`, for the cut of `C` at `(1, j, λ)`. -/
noncomputable def crossArcCount (Rs : Fin k → List V) (C : Cell k) (j : StarIdx k) (lam : ℝ) :
    ℕ :=
  ∑ l : Fin k, ((arcs (Rs l)).filter fun e => decide
    ((e.1 ∈ G.cellVerts (C.lower j lam) ∧ e.2 ∈ G.cellVerts (C.upper j lam)) ∨
     (e.1 ∈ G.cellVerts (C.upper j lam) ∧ e.2 ∈ G.cellVerts (C.lower j lam)))).length

/-- The root cell `C_0` of def:construction: the bounds are the minimum and the maximum of each
star coordinate over all vertices. -/
noncomputable def rootCell : Cell k where
  lo j := Finset.univ.inf' ⟨G.s 0, Finset.mem_univ _⟩ (G.starX j)
  hi j := Finset.univ.sup' ⟨G.s 0, Finset.mem_univ _⟩ (G.starX j)
  lo_le_hi _ := le_trans (Finset.inf'_le _ (Finset.mem_univ (G.s 0)))
    (Finset.le_sup' _ (Finset.mem_univ (G.s 0)))

/-- The level `λ` is good for the cut of `C` in `X_{1j}` (cor:goodlevel): generic,
in `[m + θE, M - θE]` where `E = w(C)` and `[m, M] = [a_j, b_j]` is the range of `X_{1j}` on
`C`, and crossed at most `3k - 4` times. -/
def IsGoodLevel (Rs : Fin k → List V) (C : Cell k) (j : StarIdx k) (lam : ℝ) : Prop :=
  G.IsGeneric j lam ∧ C.lo j + theta k * C.width ≤ lam ∧ lam ≤ C.hi j - theta k * C.width ∧
    G.crossNum Rs C j lam ≤ 3 * k - 4

/-- def:construction, one step: `C` is not a leaf (`V(C)` meets two point classes), `X_{1j}` is
a widest star coordinate of `C`, and `λ` is a good level. -/
def ConstrCut (Rs : Fin k → List V) (C : Cell k) (j : StarIdx k) (lam : ℝ) : Prop :=
  ¬ G.AtMostOneClass (G.cellVerts C) ∧ C.ext 0 j.1 = C.width ∧ G.IsGoodLevel Rs C j lam

/-- `C'` is a child of `C` under some step of def:construction. -/
def ConstrStep (Rs : Fin k → List V) (C' C : Cell k) : Prop :=
  ∃ j lam, G.ConstrCut Rs C j lam ∧ (C' = C.lower j lam ∨ C' = C.upper j lam)

/-- def:construction.  A (finite) tree built by the rule of the construction from the cell `C`:
a cell is a leaf iff `V(C)` meets at most one point class, and otherwise it is cut at a widest
star coordinate at a good level. -/
def IsConstructionTree (Rs : Fin k → List V) : CutTree k → Cell k → Prop
  | .leaf, C => G.AtMostOneClass (G.cellVerts C)
  | .node j lam lt rt, C =>
      G.ConstrCut Rs C j lam ∧
        IsConstructionTree Rs lt (C.lower j lam) ∧ IsConstructionTree Rs rt (C.upper j lam)

end Instance

end DSPP
