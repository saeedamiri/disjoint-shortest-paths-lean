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
  have lp := G.len_pos u v huv
  have hAle : ∀ x : V, (if G.Reach (G.s j) x then min (G.dist (G.s j) x) (G.d j) else G.d j)
      ≤ G.d j := by
    intro x
    split_ifs
    · exact min_le_right _ _
    · exact le_rfl
  have hBnn : ∀ x : V, 0 ≤ (if G.Reach x (G.t j) then max (G.d j - G.dist x (G.t j)) 0 else 0) := by
    intro x
    split_ifs
    · exact le_max_right _ _
    · exact le_rfl
  have hA : (if G.Reach (G.s j) v then min (G.dist (G.s j) v) (G.d j) else G.d j) ≤
      (if G.Reach (G.s j) u then min (G.dist (G.s j) u) (G.d j) else G.d j) + G.len u v := by
    by_cases hu : G.Reach (G.s j) u
    · obtain ⟨hv, hle⟩ := G.dist_le_dist_add_len hu huv
      rw [if_pos hv, if_pos hu]
      rcases le_total (G.dist (G.s j) u) (G.d j) with h | h
      · rw [min_eq_left h]
        exact (min_le_left _ _).trans (by linarith)
      · rw [min_eq_right h]
        linarith [min_le_right (G.dist (G.s j) v) (G.d j)]
    · rw [if_neg hu]
      linarith [hAle v]
  have hB : (if G.Reach v (G.t j) then max (G.d j - G.dist v (G.t j)) 0 else 0) ≤
      (if G.Reach u (G.t j) then max (G.d j - G.dist u (G.t j)) 0 else 0) + G.len u v := by
    by_cases hv : G.Reach v (G.t j)
    · obtain ⟨hu, hle⟩ := G.dist_le_len_add_dist hv huv
      rw [if_pos hv, if_pos hu]
      rcases le_total (G.d j - G.dist v (G.t j)) 0 with h | h
      · rw [max_eq_right h]
        linarith [le_max_right (G.d j - G.dist u (G.t j)) 0]
      · rw [max_eq_left h]
        linarith [le_max_left (G.d j - G.dist u (G.t j)) 0]
    · rw [if_neg hv]
      linarith [hBnn u]
  refine ⟨?_, fun hin => ?_⟩
  · unfold F
    linarith
  · obtain ⟨_, hsu, hvt, heq⟩ := hin
    obtain ⟨hsv, h1, h2, hut, h3, h4⟩ := G.lem_Di_a (i := j) ⟨huv, hsu, hvt, heq⟩
    have n1 := G.dist_nonneg (G.s j) u
    have n2 := G.dist_nonneg v (G.t j)
    unfold F
    rw [if_pos hsv, if_pos hsu, if_pos hvt, if_pos hut,
      min_eq_left (by linarith : G.dist (G.s j) v ≤ G.d j),
      min_eq_left (by linarith : G.dist (G.s j) u ≤ G.d j),
      max_eq_left (by linarith : 0 ≤ G.d j - G.dist v (G.t j)),
      max_eq_left (by linarith : 0 ≤ G.d j - G.dist u (G.t j))]
    linarith

/-- lem:W12 (W1).  Along an arc of `D_l` the coordinates `X_{lj}` do not decrease, and every
other coordinate changes by at most the increase of the two monotone ones. -/
theorem lem_W1 {l : Fin k} {u v : V} (h : G.inD l u v) :
    (∀ j, j ≠ l → 0 ≤ G.Xv l j v - G.Xv l j u) ∧
    (∀ i j, i ≠ l → j ≠ l →
      |G.Xv i j v - G.Xv i j u| ≤ (G.Xv l i v - G.Xv l i u) + (G.Xv l j v - G.Xv l j u)) := by
  have hl := (G.lem_W0 h.1 l).2 h
  have hj := fun j => (G.lem_W0 h.1 j).1
  simp only [Instance.Xv, X, Instance.pt]
  refine ⟨fun j _ => by linarith [hj j], fun i j _ _ => ?_⟩
  rw [abs_le]; constructor <;> linarith [hj i, hj j]

/-- lem:W12 (W2).  An arc of `D_l` inside a point class increases every potential by exactly
`2ℓ(u,v) > 0`. -/
theorem lem_W2 {l : Fin k} {u v : V} (h : G.inD l u v) (hc : G.SameClass u v) :
    0 < 2 * G.len u v ∧ ∀ j, G.F j v - G.F j u = 2 * G.len u v := by
  have hl := (G.lem_W0 h.1 l).2 h
  refine ⟨by linarith [G.len_pos u v h.1], fun j => ?_⟩
  have := hc l j
  simp only [Instance.Xv, X, Instance.pt] at this
  linarith

/-- Point classes are determined by the star coordinates (text after the definition of point
classes). -/
theorem sameClass_iff_star [NeZero k] (u v : V) :
    G.SameClass u v ↔ ∀ j : StarIdx k, G.Xv 0 j u = G.Xv 0 j v := by
  refine ⟨fun h j => h 0 j, fun h i j => ?_⟩
  have key : ∀ i : Fin k, G.Xv 0 i u = G.Xv 0 i v := by
    intro i
    by_cases hi : i = 0
    · subst hi; simp [Instance.Xv, X]
    · exact h ⟨i, hi⟩
  have h1 := key i; have h2 := key j
  simp only [Instance.Xv, X] at *
  linarith

/-- lem:classpiece.  The positions of a `D_l`-path that lie in one point class form an interval
of integers. -/
theorem lem_classpiece {l : Fin k} {R : List V} (hR : G.IsDPath l R) {a b c : ℕ}
    (hab : a ≤ b) (hbc : b ≤ c) (hc : c < R.length)
    (hac : G.SameClass (R[a]'(by omega)) (R[c]'hc)) :
    G.SameClass (R[a]'(by omega)) (R[b]'(by omega)) := by
  obtain ⟨_, hch, _⟩ := hR
  rw [List.isChain_iff_getElem] at hch
  have mono : ∀ n (p : ℕ) (hp : p + n < R.length) (j : Fin k),
      G.Xv l j (R[p]'(by omega)) ≤ G.Xv l j (R[p + n]'hp) := by
    intro n
    induction n with
    | zero => intro p hp j; exact le_rfl
    | succ n ih =>
      intro p hp j
      have h1 := ih p (by omega) j
      have h2 : G.Xv l j (R[p + n]'(by omega)) ≤ G.Xv l j (R[p + n + 1]'(by omega)) := by
        have := G.lem_W1 (hch (p + n) (by omega))
        by_cases hj : j = l
        · subst hj; simp [Instance.Xv, X]
        · have := this.1 j hj
          linarith
      exact h1.trans h2
  obtain ⟨n1, rfl⟩ := Nat.exists_eq_add_of_le hab
  obtain ⟨n2, rfl⟩ := Nat.exists_eq_add_of_le hbc
  intro i j
  have key : ∀ j', G.Xv l j' (R[a]'(by omega)) = G.Xv l j' (R[a + n1]'(by omega)) := by
    intro j'
    have e1 := mono n1 a (by omega) j'
    have e2 := mono n2 (a + n1) (by omega) j'
    have e3 := hac l j'
    have : R[a + n1 + n2]'hc = R[a + (n1 + n2)]'(by omega) := by simp [Nat.add_assoc]
    rw [this] at e2 e3
    have e4 := mono (n1 + n2) a (by omega) j'
    have e5 : G.Xv l j' (R[a + n1 + n2]'hc) = G.Xv l j' (R[a + (n1 + n2)]'(by omega)) := by
      simp [Nat.add_assoc]
    linarith
  have hx : ∀ x : V, G.Xv i j x = G.Xv l j x - G.Xv l i x := by
    intro x; simp only [Instance.Xv, X]; ring
  rw [hx, hx, key i, key j]

end Instance

end DSPP
