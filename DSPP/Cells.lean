/-
Cells, extents, width; lem:extent.

Paper: "Directed k Disjoint Shortest Paths Is Polynomial for Every Fixed k" (Saeed Amiri),
Section "Preliminaries", subsection "Cells" (def:cell, lem:extent).
-/
import DSPP.Potentials

open Classical

namespace DSPP

variable {k : ℕ} [NeZero k]

/-- def:cell.  A cell is given by real bounds `a_j ≤ b_j` on the star coordinates
`X_{1j}`, `j = 2, ..., k`. -/
structure Cell (k : ℕ) [NeZero k] where
  /-- Lower bounds `a_j`. -/
  lo : StarIdx k → ℝ
  /-- Upper bounds `b_j`. -/
  hi : StarIdx k → ℝ
  /-- `a_j ≤ b_j`. -/
  lo_le_hi : ∀ j, lo j ≤ hi j

namespace Cell

/-- The point set `C = {x ∈ ℝ^k : a_j ≤ X_{1j}(x) ≤ b_j for all j}`. -/
def carrier (C : Cell k) : Set (Fin k → ℝ) :=
  {x | ∀ j : StarIdx k, C.lo j ≤ X 0 j.1 x ∧ X 0 j.1 x ≤ C.hi j}

/-- The extent `ext_{ij}(C) = max_C X_{ij} - min_C X_{ij}`. -/
noncomputable def ext (C : Cell k) (i j : Fin k) : ℝ :=
  sSup (X i j '' C.carrier) - sInf (X i j '' C.carrier)

/-- The width `w(C) = max_{2 ≤ j ≤ k} ext_{1j}(C)`. -/
noncomputable def width (C : Cell k) : ℝ := ⨆ j : StarIdx k, C.ext 0 j.1

/-- The child `C ∩ {X_{1j} ≤ λ}` of a cut at `(1,j,λ)`: the upper bound in `X_{1j}` is replaced
by `λ` (clamped from below by `a_j` so that the bounds stay valid; in a hierarchy
`a_j < λ < b_j`, and then this is exactly the cell of lem:extent (c)). -/
noncomputable def lower (C : Cell k) (j : StarIdx k) (lam : ℝ) : Cell k where
  lo := C.lo
  hi := Function.update C.hi j (max (C.lo j) lam)
  lo_le_hi := by
    intro j'
    by_cases h : j' = j
    · subst h; simp
    · simp [Function.update_of_ne h, C.lo_le_hi j']

/-- The child `C ∩ {X_{1j} ≥ λ}` of a cut at `(1,j,λ)`: the lower bound in `X_{1j}` is replaced
by `λ` (clamped from above by `b_j`). -/
noncomputable def upper (C : Cell k) (j : StarIdx k) (lam : ℝ) : Cell k where
  lo := Function.update C.lo j (min (C.hi j) lam)
  hi := C.hi
  lo_le_hi := by
    intro j'
    by_cases h : j' = j
    · subst h; simp
    · simp [Function.update_of_ne h, C.lo_le_hi j']

/-- lem:extent (a).  The star map sends `C` onto the box `∏ [a_j, b_j]`; `C` is non-empty,
closed, convex and invariant under adding multiples of `𝟙`. -/
theorem lem_extent_a (C : Cell k) :
    (fun x : Fin k → ℝ => fun j : StarIdx k => X 0 j.1 x) '' C.carrier =
        Set.pi Set.univ (fun j => Set.Icc (C.lo j) (C.hi j)) ∧
      C.carrier.Nonempty ∧ IsClosed C.carrier ∧ Convex ℝ C.carrier ∧
      ∀ x ∈ C.carrier, ∀ c : ℝ, x + c • one k ∈ C.carrier := by
  sorry

/-- lem:extent (b).  `ext_{1j}(C) = E_j`, `ext_{ij}(C) = E_i + E_j` for star indices `i ≠ j`,
`w(C) = max_j E_j`, every extent is at most `2 w(C)`, and the bounds are the extreme values of
`X_{1j}` on `C`. -/
theorem lem_extent_b (C : Cell k) :
    (∀ j : StarIdx k, C.ext 0 j.1 = C.hi j - C.lo j) ∧
    (∀ i j : StarIdx k, i ≠ j → C.ext i.1 j.1 = (C.hi i - C.lo i) + (C.hi j - C.lo j)) ∧
    (∀ i j : Fin k, C.ext i j = C.ext j i) ∧
    C.width = ⨆ j : StarIdx k, (C.hi j - C.lo j) ∧
    (∀ i j : Fin k, C.ext i j ≤ 2 * C.width) ∧
    (∀ j : StarIdx k, IsLeast (X 0 j.1 '' C.carrier) (C.lo j) ∧
      IsGreatest (X 0 j.1 '' C.carrier) (C.hi j)) := by
  sorry

/-- lem:extent (c).  Cutting a cell by a half-space of a star coordinate gives the cell with
one bound replaced, or the empty set. -/
theorem lem_extent_c (C : Cell k) (j : StarIdx k) (lam : ℝ) :
    (C.lo j ≤ lam → C.carrier ∩ {x | X 0 j.1 x ≤ lam} = (C.lower j (min (C.hi j) lam)).carrier) ∧
    (lam < C.lo j → C.carrier ∩ {x | X 0 j.1 x ≤ lam} = ∅) ∧
    (lam ≤ C.hi j → C.carrier ∩ {x | lam ≤ X 0 j.1 x} = (C.upper j (max (C.lo j) lam)).carrier) ∧
    (C.hi j < lam → C.carrier ∩ {x | lam ≤ X 0 j.1 x} = ∅) := by
  sorry

end Cell

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace Instance

variable (G : Instance V k)

/-- The value of the star coordinate `X_{1j}` at a vertex. -/
noncomputable def starX (j : StarIdx k) (v : V) : ℝ := G.Xv 0 j.1 v

/-- `V(C) = {v ∈ V : π(v) ∈ C}`. -/
noncomputable def cellVerts (C : Cell k) : Finset V :=
  Finset.univ.filter fun v => G.pt v ∈ C.carrier

end Instance

end DSPP
