/-
Potentials, points, coordinates, point classes; (W0), (W1), (W2), lem:classpiece.

Paper: "Directed k Disjoint Shortest Paths Is Polynomial for Every Fixed k" (Saeed Amiri),
Section "Preliminaries", subsections "Potentials" and "Points, coordinates and monotonicity".

Index convention: the paper's index `1` is `0 : Fin k`; the star coordinates `X_{1j}`,
`j = 2, ..., k`, are indexed by `StarIdx k = {j : Fin k // j ≠ 0}`.
-/
import DSPP.ShortestDAG

open Classical

namespace DSPP

/-- Indices of the star coordinates `X_{1j}`, `j ≠ 1` (here: `j ≠ 0`).  There are `k - 1`. -/
abbrev StarIdx (k : ℕ) [NeZero k] := {j : Fin k // j ≠ 0}

/-- The coordinate `X_{ij}(x) = x_i - x_j` on `ℝ^k`. -/
def X {k : ℕ} (i j : Fin k) (x : Fin k → ℝ) : ℝ := x i - x j

/-- The all-ones vector `𝟙`. -/
def one (k : ℕ) : Fin k → ℝ := fun _ => 1

variable {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}

namespace Instance

variable (G : Instance V k)

/-- def:potentials.
`F_i(v) = min(d(s_i,v), d_i) + max(d_i - d(v,t_i), 0)` with `min(∞, d_i) = d_i` and
`max(-∞, 0) = 0`. -/
noncomputable def F (i : Fin k) (v : V) : ℝ :=
  (if G.Reach (G.s i) v then min (G.dist (G.s i) v) (G.d i) else G.d i) +
    (if G.Reach v (G.t i) then max (G.d i - G.dist v (G.t i)) 0 else 0)

/-- The point `π(v) = (F_1(v), ..., F_k(v))`. -/
noncomputable def pt (v : V) : Fin k → ℝ := fun i => G.F i v

/-- `X_{ij}(v) = X_{ij}(π(v))`. -/
noncomputable def Xv (i j : Fin k) (v : V) : ℝ := X i j (G.pt v)

/-- Same point class: `π(u) - π(v) ∈ ℝ𝟙`, that is, `X_{ij}(u) = X_{ij}(v)` for all `i, j`. -/
def SameClass (u v : V) : Prop := ∀ i j : Fin k, G.Xv i j u = G.Xv i j v

/-- lem:W0.  Along every arc each potential increases by at most `2ℓ(u,v)`, with equality on
the arcs of `D_j`. -/
theorem lem_W0 {u v : V} (huv : G.arc u v) (j : Fin k) :
    G.F j v - G.F j u ≤ 2 * G.len u v ∧ (G.inD j u v → G.F j v - G.F j u = 2 * G.len u v) := by
  sorry

/-- lem:W12 (W1).  Along an arc of `D_l` the coordinates `X_{lj}` do not decrease, and every
other coordinate changes by at most the increase of the two monotone ones. -/
theorem lem_W1 {l : Fin k} {u v : V} (h : G.inD l u v) :
    (∀ j, j ≠ l → 0 ≤ G.Xv l j v - G.Xv l j u) ∧
    (∀ i j, i ≠ l → j ≠ l →
      |G.Xv i j v - G.Xv i j u| ≤ (G.Xv l i v - G.Xv l i u) + (G.Xv l j v - G.Xv l j u)) := by
  sorry

/-- lem:W12 (W2).  An arc of `D_l` inside a point class increases every potential by exactly
`2ℓ(u,v) > 0`. -/
theorem lem_W2 {l : Fin k} {u v : V} (h : G.inD l u v) (hc : G.SameClass u v) :
    0 < 2 * G.len u v ∧ ∀ j, G.F j v - G.F j u = 2 * G.len u v := by
  sorry

/-- Point classes are determined by the star coordinates (text after the definition of point
classes). -/
theorem sameClass_iff_star [NeZero k] (u v : V) :
    G.SameClass u v ↔ ∀ j : StarIdx k, G.Xv 0 j u = G.Xv 0 j v := by
  sorry

/-- lem:classpiece.  The positions of a `D_l`-path that lie in one point class form an interval
of integers. -/
theorem lem_classpiece {l : Fin k} {R : List V} (hR : G.IsDPath l R) {a b c : ℕ}
    (hab : a ≤ b) (hbc : b ≤ c) (hc : c < R.length)
    (hac : G.SameClass (R[a]'(by omega)) (R[c]'hc)) :
    G.SameClass (R[a]'(by omega)) (R[b]'(by omega)) := by
  sorry

end Instance

end DSPP
