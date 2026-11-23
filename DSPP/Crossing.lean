/-
Curves, generic levels, the crossing number `N_C(λ)` (def:N) and pieces.

Paper: "Directed k Disjoint Shortest Paths Is Polynomial for Every Fixed k" (Saeed Amiri),
Section "Preliminaries", subsection "Curves and generic levels", and the definition of pieces at
the start of Section "The cut hierarchy".

The crossing number is defined combinatorially, arc by arc (see `DEVIATIONS.md`).
-/
import DSPP.Cells

open Classical

namespace DSPP

variable {k : ℕ} [NeZero k]

/-- The point where the segment from `p` to `q` meets the hyperplane `X_{1j} = λ` (meaningful
when `X_{1j}(p) ≠ X_{1j}(q)`). -/
noncomputable def crossPt (j : StarIdx k) (lam : ℝ) (p q : Fin k → ℝ) : Fin k → ℝ :=
  p + ((lam - X 0 j.1 p) / (X 0 j.1 q - X 0 j.1 p)) • (q - p)

/-- The segment from `p` to `q` crosses the level `X_{1j} = λ` strictly (its ends lie on
different sides) at a point of the cell `C`. -/
def segCross (C : Cell k) (j : StarIdx k) (lam : ℝ) (p q : Fin k → ℝ) : Prop :=
  ((X 0 j.1 p < lam ∧ lam < X 0 j.1 q) ∨ (X 0 j.1 q < lam ∧ lam < X 0 j.1 p)) ∧
    crossPt j lam p q ∈ C.carrier

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The pieces of a vertex sequence `R` in a set `U`: the maximal runs of consecutive vertices
of `R` that lie in `U`, in order. -/
def pieces (U : Finset V) (R : List V) : List (List V) :=
  (R.splitOnP (fun v => decide (v ∉ U))).filter (fun p => !p.isEmpty)

namespace Instance

variable (G : Instance V k)

/-- `λ` is generic for `X_{1j}`: no vertex has `X_{1j}(v) = λ`. -/
def IsGeneric (j : StarIdx k) (lam : ℝ) : Prop := ∀ v : V, G.starX j v ≠ lam

/-- All but at most `n` values are generic. -/
theorem nonGeneric_finite (j : StarIdx k) :
    {lam : ℝ | ¬ G.IsGeneric j lam} = Set.range (G.starX j) := by
  ext lam; simp [IsGeneric]

/-- def:N (combinatorial form).  For a `k`-tuple `Rs` of vertex sequences, a cell `C`, a star
coordinate `X_{1j}` and a level `λ`, the number of pairs `(l, arc of R_l)` whose segment crosses
the level `λ` strictly at a point of `C`.  For generic `λ` this is the paper's `N_C(λ)`. -/
noncomputable def crossNum (Rs : Fin k → List V) (C : Cell k) (j : StarIdx k) (lam : ℝ) : ℕ :=
  ∑ l : Fin k, ((arcs (Rs l)).filter
    fun e => decide (segCross C j lam (G.pt e.1) (G.pt e.2))).length

end Instance

end DSPP
