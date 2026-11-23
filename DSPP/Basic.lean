/-
Instances, walks, paths, distances and solutions.

Formalization of "Directed k Disjoint Shortest Paths Is Polynomial for Every Fixed k"
(Saeed Amiri), Section "Preliminaries", subsection "Instances and shortest-path DAGs".
-/
import Mathlib

open Classical

namespace DSPP

/-- An instance of the directed `k` disjoint shortest paths problem.

The vertex set is the finite type `V`, `n = Fintype.card V`.  Arcs are given by the relation
`arc`, so there are no parallel arcs (the paper removes them without loss of generality, see
`DEVIATIONS.md`).  The terminal pairs are `(s l, t l)` for `l : Fin k`; the `2k` terminals are
pairwise distinct. -/
structure Instance (V : Type*) [Fintype V] [DecidableEq V] (k : ℕ) where
  /-- The arc relation of the directed graph. -/
  arc : V → V → Prop
  /-- The length function; only its values on arcs matter. -/
  len : V → V → ℝ
  /-- Lengths are strictly positive on arcs. -/
  len_pos : ∀ u v, arc u v → 0 < len u v
  /-- Sources. -/
  s : Fin k → V
  /-- Sinks. -/
  t : Fin k → V
  /-- The `2k` terminals are pairwise distinct. -/
  terminals_injective : Function.Injective (Sum.elim s t)
  /-- At least two pairs. -/
  two_le_k : 2 ≤ k

variable {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}

/-- The arcs `(v_q, v_{q+1})` of a vertex sequence, in order. -/
def arcs (R : List V) : List (V × V) := R.zip R.tail

namespace Instance

variable (G : Instance V k)

/-- `R` is a walk from `a` to `b`: a non-empty vertex sequence starting at `a`, ending at `b`,
with consecutive vertices joined by arcs. -/
def IsWalk (R : List V) (a b : V) : Prop :=
  R.head? = some a ∧ R.getLast? = some b ∧ R.IsChain G.arc

/-- `R` is a (simple, directed) path from `a` to `b`.  A path may consist of a single vertex. -/
def IsPath (R : List V) (a b : V) : Prop :=
  G.IsWalk R a b ∧ R.Nodup

/-- The length of a vertex sequence: the sum of the lengths of its arcs. -/
noncomputable def wlen (R : List V) : ℝ :=
  ((arcs R).map fun e => G.len e.1 e.2).sum

/-- `b` is reachable from `a`. -/
def Reach (a b : V) : Prop := ∃ R, G.IsWalk R a b

/-- The distance `d(a,b)`: the infimum of the lengths of the walks from `a` to `b`.  It is only
meaningful when `G.Reach a b`; for unreachable pairs its value (`0`) is never used, every
statement that involves it also involves `Reach`.  With positive lengths the infimum over walks
equals the minimum over paths (`dist_eq_min_path`). -/
noncomputable def dist (a b : V) : ℝ :=
  sInf {x | ∃ R, G.IsWalk R a b ∧ G.wlen R = x}

/-- `d_i = d(s_i, t_i)`. -/
noncomputable def d (i : Fin k) : ℝ := G.dist (G.s i) (G.t i)

/-- `R` is a shortest path from `a` to `b`: a path that is not longer than any other path from
`a` to `b`. -/
def IsShortestPath (R : List V) (a b : V) : Prop :=
  G.IsPath R a b ∧ ∀ R', G.IsPath R' a b → G.wlen R ≤ G.wlen R'

/-- A solution: pairwise vertex-disjoint paths `P_1, ..., P_k`, where `P_i` is a shortest
`s_i`--`t_i` path. -/
def IsSolution (P : Fin k → List V) : Prop :=
  (∀ i, G.IsShortestPath (P i) (G.s i) (G.t i)) ∧
    ∀ i j, i ≠ j → ∀ v ∈ P i, v ∉ P j

/-- The instance has a solution. -/
def HasSolution : Prop := ∃ P : Fin k → List V, G.IsSolution P

/-! ### Basic facts about walks and distances -/

theorem wlen_nil : G.wlen [] = 0 := by simp [wlen, arcs]

theorem wlen_singleton (a : V) : G.wlen [a] = 0 := by simp [wlen, arcs]

theorem wlen_cons_cons (a b : V) (R : List V) :
    G.wlen (a :: b :: R) = G.len a b + G.wlen (b :: R) := by
  simp [wlen, arcs]

theorem wlen_append_cons (A : List V) (b : V) (S : List V) :
    G.wlen (A ++ b :: S) = G.wlen (A ++ [b]) + G.wlen (b :: S) := by
  induction A with
  | nil => simp [wlen_singleton]
  | cons x A ih =>
    cases A with
    | nil => simp [wlen_cons_cons, wlen_singleton]
    | cons y A =>
      have h1 := ih
      simp only [List.cons_append] at h1 ⊢
      rw [wlen_cons_cons, wlen_cons_cons, h1]
      ring

theorem wlen_cons_ge {x : V} {R : List V} (h : (x :: R).IsChain G.arc) :
    G.wlen R ≤ G.wlen (x :: R) := by
  cases R with
  | nil => simp [wlen_nil, wlen_singleton]
  | cons y R =>
    rw [wlen_cons_cons]
    have : 0 < G.len x y := G.len_pos _ _ (List.isChain_cons_cons.mp h).1
    linarith

theorem wlen_suffix_le {P : List V} {a : V} {Q : List V} (h : (P ++ a :: Q).IsChain G.arc) :
    G.wlen (a :: Q) ≤ G.wlen (P ++ a :: Q) := by
  induction P with
  | nil => simp
  | cons x P ih =>
    have := ih h.tail
    have h2 : G.wlen (P ++ a :: Q) ≤ G.wlen (x :: (P ++ a :: Q)) := G.wlen_cons_ge h
    simp only [List.cons_append]
    linarith

theorem wlen_nonneg_of_chain {R : List V} (h : R.IsChain G.arc) : 0 ≤ G.wlen R := by
  induction R with
  | nil => simp [wlen_nil]
  | cons x R ih =>
    have := ih h.tail
    have h2 := G.wlen_cons_ge h
    linarith

/-- Lengths of walks are non-negative. -/
theorem wlen_nonneg {R : List V} {a b : V} (h : G.IsWalk R a b) : 0 ≤ G.wlen R :=
  G.wlen_nonneg_of_chain h.2.2

theorem walk_set_nonempty {a b : V} (h : G.Reach a b) :
    {x | ∃ R, G.IsWalk R a b ∧ G.wlen R = x}.Nonempty := by
  obtain ⟨R, hR⟩ := h
  exact ⟨_, R, hR, rfl⟩

theorem walk_set_bdd (a b : V) : BddBelow {x | ∃ R, G.IsWalk R a b ∧ G.wlen R = x} := by
  refine ⟨0, ?_⟩
  rintro x ⟨R, hR, rfl⟩
  exact G.wlen_nonneg hR

/-- The distance is a lower bound for the length of every walk. -/
theorem dist_le_wlen {R : List V} {a b : V} (h : G.IsWalk R a b) : G.dist a b ≤ G.wlen R :=
  csInf_le (G.walk_set_bdd a b) ⟨R, h, rfl⟩

/-- Distances are non-negative. -/
theorem dist_nonneg (a b : V) : 0 ≤ G.dist a b := by
  by_cases h : G.Reach a b
  · exact le_csInf (G.walk_set_nonempty h) (by rintro x ⟨R, hR, rfl⟩; exact G.wlen_nonneg hR)
  · have : {x | ∃ R, G.IsWalk R a b ∧ G.wlen R = x} = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨R, hR, _⟩
      exact h ⟨R, hR⟩
    simp [dist, this]

theorem le_dist_of {a b : V} (h : G.Reach a b) {x : ℝ}
    (hx : ∀ R, G.IsWalk R a b → x ≤ G.wlen R) : x ≤ G.dist a b :=
  le_csInf (G.walk_set_nonempty h) (by rintro y ⟨R, hR, rfl⟩; exact hx R hR)

theorem getLast?_append_cons (A : List V) (u : V) (S : List V) :
    (A ++ u :: S).getLast? = (u :: S).getLast? :=
  List.getLast?_append_of_ne_nil A (List.cons_ne_nil u S)

theorem isWalk_append {A : List V} {a u : V} {S : List V} {b : V}
    (h1 : G.IsWalk (A ++ [u]) a u) (h2 : G.IsWalk (u :: S) u b) :
    G.IsWalk (A ++ u :: S) a b := by
  obtain ⟨hh1, _, hc1⟩ := h1
  obtain ⟨_, hl2, hc2⟩ := h2
  refine ⟨?_, ?_, ?_⟩
  · cases A <;> simpa using hh1
  · rw [getLast?_append_cons]; exact hl2
  · exact List.isChain_split.mpr ⟨hc1, hc2⟩

theorem walk_decomp {W : List V} {a u : V} (h : G.IsWalk W a u) :
    ∃ A, W = A ++ [u] ∧ G.IsWalk (A ++ [u]) a u := by
  have h' := h
  obtain ⟨_, hl, _⟩ := h
  have hne : W ≠ [] := by rintro rfl; simp at hl
  obtain ⟨A, x, hW⟩ := (List.eq_nil_or_concat W).resolve_left hne
  rw [List.concat_eq_append] at hW
  subst hW
  have : x = u := by simpa using hl
  subst this
  exact ⟨A, rfl, h'⟩

/-- Triangle inequality along an arc. -/
theorem dist_le_dist_add_len {a u v : V} (hu : G.Reach a u) (huv : G.arc u v) :
    G.Reach a v ∧ G.dist a v ≤ G.dist a u + G.len u v := by
  have key : ∀ W, G.IsWalk W a u → G.IsWalk (W ++ [v]) a v ∧
      G.wlen (W ++ [v]) = G.wlen W + G.len u v := by
    intro W hW
    obtain ⟨A, rfl, hA⟩ := G.walk_decomp hW
    have hv : G.IsWalk [u, v] u v := ⟨by simp, by simp, by simpa using huv⟩
    have hw : G.IsWalk (A ++ u :: [v]) a v := G.isWalk_append hA hv
    refine ⟨by simpa using hw, ?_⟩
    have := G.wlen_append_cons A u [v]
    simp only [List.append_assoc, List.singleton_append] at this ⊢
    rw [this, wlen_cons_cons, wlen_singleton]; ring
  obtain ⟨W0, hW0⟩ := hu
  refine ⟨⟨_, (key W0 hW0).1⟩, ?_⟩
  have : G.dist a v - G.len u v ≤ G.dist a u := by
    refine G.le_dist_of ⟨W0, hW0⟩ fun W hW => ?_
    have := G.dist_le_wlen (key W hW).1
    rw [(key W hW).2] at this
    linarith
  linarith

/-- Triangle inequality along an arc, distances to a target. -/
theorem dist_le_len_add_dist {u v b : V} (hv : G.Reach v b) (huv : G.arc u v) :
    G.Reach u b ∧ G.dist u b ≤ G.len u v + G.dist v b := by
  have key : ∀ W, G.IsWalk W v b → G.IsWalk (u :: W) u b ∧
      G.wlen (u :: W) = G.len u v + G.wlen W := by
    intro W hW
    obtain ⟨h1, h2, h3⟩ := hW
    cases W with
    | nil => simp at h1
    | cons y W =>
      have hy : y = v := by simpa using h1
      subst hy
      refine ⟨⟨by simp, by simpa using h2, ?_⟩, G.wlen_cons_cons _ _ _⟩
      exact List.isChain_cons_cons.mpr ⟨huv, h3⟩
  obtain ⟨W0, hW0⟩ := hv
  refine ⟨⟨_, (key W0 hW0).1⟩, ?_⟩
  have : G.dist u b - G.len u v ≤ G.dist v b := by
    refine G.le_dist_of ⟨W0, hW0⟩ fun W hW => ?_
    have := G.dist_le_wlen (key W hW).1
    rw [(key W hW).2] at this
    linarith
  linarith

/-- Triangle inequality. -/
theorem dist_triangle {a u b : V} (h1 : G.Reach a u) (h2 : G.Reach u b) :
    G.Reach a b ∧ G.dist a b ≤ G.dist a u + G.dist u b := by
  have key : ∀ W1 W2, G.IsWalk W1 a u → G.IsWalk W2 u b → G.IsWalk (W1 ++ W2.tail) a b ∧
      G.wlen (W1 ++ W2.tail) = G.wlen W1 + G.wlen W2 := by
    intro W1 W2 hW1 hW2
    obtain ⟨A, rfl, hA⟩ := G.walk_decomp hW1
    have h21 := hW2.1
    cases W2 with
    | nil => simp at h21
    | cons y S =>
      have hy : y = u := by simpa using h21
      subst hy
      have hw := G.isWalk_append hA hW2
      refine ⟨by simpa using hw, ?_⟩
      have := G.wlen_append_cons A y S
      simp only [List.append_assoc, List.singleton_append, List.tail_cons] at this ⊢
      rw [this]
  obtain ⟨W1, hW1⟩ := h1
  obtain ⟨W2, hW2⟩ := h2
  refine ⟨⟨_, (key W1 W2 hW1 hW2).1⟩, ?_⟩
  have h3 : G.dist a b - G.dist u b ≤ G.dist a u := by
    refine G.le_dist_of ⟨W1, hW1⟩ fun W hW => ?_
    have h4 : G.dist a b - G.wlen W ≤ G.dist u b := by
      refine G.le_dist_of ⟨W2, hW2⟩ fun W' hW' => ?_
      have := G.dist_le_wlen (key W W' hW hW').1
      rw [(key W W' hW hW').2] at this
      linarith
    linarith
  linarith

/-- Shortcutting: every walk contains a path with the same ends that is not longer
(lengths are positive). -/
theorem exists_path_of_walk {W : List V} {a b : V} (h : G.IsWalk W a b) :
    ∃ R, G.IsPath R a b ∧ G.wlen R ≤ G.wlen W ∧ ∀ v ∈ R, v ∈ W := by
  induction W generalizing a with
  | nil => simp [IsWalk] at h
  | cons x rest ih =>
    obtain ⟨h1, h2, h3⟩ := h
    have hxa : x = a := by simpa using h1
    subst hxa
    cases rest with
    | nil =>
      have : x = b := by simpa using h2
      subst this
      exact ⟨[x], ⟨⟨by simp, by simp, by simp⟩, by simp⟩, by simp, by simp⟩
    | cons c rest' =>
      have harc : G.arc x c := (List.isChain_cons_cons.mp h3).1
      have hw : G.IsWalk (c :: rest') c b := ⟨by simp, h2.trans (by simp), h3.tail⟩
      obtain ⟨R', ⟨⟨hh', hl', hc'⟩, hnd'⟩, hlen', hsub'⟩ := ih hw
      have hpos : 0 < G.len x c := G.len_pos _ _ harc
      have hwW : G.wlen (x :: c :: rest') = G.len x c + G.wlen (c :: rest') :=
        G.wlen_cons_cons _ _ _
      by_cases hx : x ∈ R'
      · obtain ⟨P, Q, hPQ⟩ := List.append_of_mem hx
        subst hPQ
        refine ⟨x :: Q, ⟨⟨by simp, ?_, ?_⟩, ?_⟩, ?_, ?_⟩
        · rw [← getLast?_append_cons P x Q]; exact hl'
        · exact hc'.suffix (List.suffix_append P (x :: Q))
        · exact List.Nodup.sublist (List.suffix_append P (x :: Q)).sublist hnd'
        · have := G.wlen_suffix_le hc'
          linarith
        · intro v hv
          rcases List.mem_cons.mp hv with rfl | hv
          · simp
          · exact List.mem_cons_of_mem _
              (hsub' v (List.mem_append_right P (List.mem_cons_of_mem _ hv)))
      · obtain ⟨R'', rfl⟩ : ∃ R'', R' = c :: R'' := by
          cases R' with
          | nil => simp at hh'
          | cons z R'' =>
            have : z = c := by simpa using hh'
            subst this; exact ⟨R'', rfl⟩
        refine ⟨x :: c :: R'', ⟨⟨by simp, ?_, ?_⟩, ?_⟩, ?_, ?_⟩
        · rw [List.getLast?_cons_cons]; exact hl'
        · exact List.isChain_cons_cons.mpr ⟨harc, hc'⟩
        · exact List.nodup_cons.mpr ⟨hx, hnd'⟩
        · rw [hwW, G.wlen_cons_cons]; linarith
        · intro v hv
          rcases List.mem_cons.mp hv with rfl | hv
          · simp
          · exact List.mem_cons_of_mem _ (hsub' v hv)

theorem finite_paths (a b : V) : {R : List V | G.IsPath R a b}.Finite := by
  refine (List.finite_length_le V (Fintype.card V)).subset ?_
  intro R hR
  exact hR.2.length_le_card

/-- A vertex reaches itself at distance `0`. -/
theorem reach_self (a : V) : G.Reach a a := ⟨[a], by simp, by simp, by simp⟩

theorem dist_self (a : V) : G.dist a a = 0 := by
  refine le_antisymm ?_ (G.dist_nonneg a a)
  have h : G.IsWalk [a] a a := ⟨by simp, by simp, by simp⟩
  have := G.dist_le_wlen h
  rwa [G.wlen_singleton] at this

/-- With positive lengths the distance is attained by a path. -/
theorem dist_eq_min_path {a b : V} (h : G.Reach a b) :
    ∃ R, G.IsPath R a b ∧ G.wlen R = G.dist a b := by
  obtain ⟨W, hW⟩ := h
  obtain ⟨R0, hR0, _⟩ := G.exists_path_of_walk hW
  obtain ⟨R, hR, hmin⟩ := Set.exists_min_image {R : List V | G.IsPath R a b} G.wlen
    (G.finite_paths a b) ⟨R0, hR0⟩
  refine ⟨R, hR, le_antisymm ?_ (G.dist_le_wlen hR.1)⟩
  refine G.le_dist_of ⟨W, hW⟩ fun W' hW' => ?_
  obtain ⟨R', hR', hle, _⟩ := G.exists_path_of_walk hW'
  exact (hmin R' hR').trans hle

/-- A path is shortest if and only if its length is the distance. -/
theorem isShortestPath_iff {R : List V} {a b : V} :
    G.IsShortestPath R a b ↔ G.IsPath R a b ∧ G.wlen R = G.dist a b := by
  constructor
  · rintro ⟨hR, hmin⟩
    obtain ⟨R0, hR0, hlen⟩ := G.dist_eq_min_path ⟨R, hR.1⟩
    exact ⟨hR, le_antisymm (hlen ▸ hmin R0 hR0) (G.dist_le_wlen hR.1)⟩
  · rintro ⟨hR, hlen⟩
    refine ⟨hR, fun R' hR' => ?_⟩
    rw [hlen]; exact G.dist_le_wlen hR'.1

end Instance

end DSPP
