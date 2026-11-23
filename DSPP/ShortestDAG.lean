/-
The shortest-path DAGs `D_i` (def:Di, lem:Di).

Paper: "Directed k Disjoint Shortest Paths Is Polynomial for Every Fixed k" (Saeed Amiri),
Section "Preliminaries".
-/
import DSPP.Basic

open Classical

namespace DSPP

variable {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}

namespace Instance

variable (G : Instance V k)

/-- def:Di.  The arc `(u,v)` lies in `D_i`: `d(s_i,u) + ℓ(u,v) + d(v,t_i) = d_i`.
The paper uses extended reals; an equation with the finite value `d_i` forces both distances
on the left to be finite, which is what the two `Reach` conditions say.  If `t_i` is not
reachable from `s_i`, then `D_i` is empty. -/
def inD (i : Fin k) (u v : V) : Prop :=
  G.arc u v ∧ G.Reach (G.s i) u ∧ G.Reach v (G.t i) ∧
    G.dist (G.s i) u + G.len u v + G.dist v (G.t i) = G.d i

/-- def:Di.  A `D_i`-path: a (simple) path all of whose arcs lie in `D_i`.  Its end vertices
are arbitrary. -/
def IsDPath (i : Fin k) (R : List V) : Prop :=
  R ≠ [] ∧ R.IsChain (G.inD i) ∧ R.Nodup

/-- lem:Di (a). -/
theorem lem_Di_a {i : Fin k} {u v : V} (h : G.inD i u v) :
    G.Reach (G.s i) v ∧ G.dist (G.s i) v = G.dist (G.s i) u + G.len u v ∧
      G.dist (G.s i) v ≤ G.d i ∧
    G.Reach u (G.t i) ∧ G.dist u (G.t i) = G.len u v + G.dist v (G.t i) ∧
      G.dist u (G.t i) ≤ G.d i := by
  obtain ⟨harc, hsu, hvt, heq⟩ := h
  obtain ⟨hsv, h1⟩ := G.dist_le_dist_add_len hsu harc
  obtain ⟨hut, h2⟩ := G.dist_le_len_add_dist hvt harc
  have h3 := (G.dist_triangle hsv hvt).2
  have h4 := (G.dist_triangle hsu hut).2
  have hd : G.d i = G.dist (G.s i) (G.t i) := rfl
  have n1 := G.dist_nonneg (G.s i) u
  have n2 := G.dist_nonneg v (G.t i)
  have n3 := G.dist_nonneg (G.s i) v
  have n4 := G.dist_nonneg u (G.t i)
  have l := G.len_pos u v harc
  refine ⟨hsv, by linarith, by linarith, hut, by linarith, by linarith⟩

/-- Along a chain of `D_i`-arcs the length is the difference of the distances from `s_i`. -/
theorem wlen_of_chain_inD (i : Fin k) :
    ∀ (R : List V) (x l : V), (x :: R).IsChain (G.inD i) → (x :: R).getLast? = some l →
      G.wlen (x :: R) = G.dist (G.s i) l - G.dist (G.s i) x := by
  intro R
  induction R with
  | nil =>
    intro x l _ hl
    have : x = l := by simpa using hl
    subst this
    simp [wlen_singleton]
  | cons y R ih =>
    intro x l hc hl
    obtain ⟨hxy, hc'⟩ := List.isChain_cons_cons.mp hc
    rw [wlen_cons_cons, ih y l hc' (by rwa [List.getLast?_cons_cons] at hl)]
    have := (G.lem_Di_a hxy).2.1
    linarith

/-- lem:Di (b).  A path from `s_i` to `t_i` is a shortest path if and only if it is a
`D_i`-path. -/
theorem lem_Di_b {i : Fin k} {R : List V} (h : G.IsPath R (G.s i) (G.t i)) :
    G.IsShortestPath R (G.s i) (G.t i) ↔ R.IsChain (G.inD i) := by
  have hd : G.d i = G.dist (G.s i) (G.t i) := rfl
  rw [G.isShortestPath_iff]
  constructor
  · rintro ⟨_, hlen⟩
    rw [List.isChain_iff_forall_rel_of_append_cons_cons]
    intro u v A B hR
    obtain ⟨⟨hh, hl, hc⟩, _⟩ := h
    subst hR
    obtain ⟨hc1, huv, hc2⟩ := List.isChain_append_cons_cons.mp hc
    have w1 : G.IsWalk (A ++ [u]) (G.s i) u := by
      refine ⟨?_, by simp, hc1⟩
      cases A <;> simpa using hh
    have w2 : G.IsWalk (v :: B) v (G.t i) := by
      refine ⟨by simp, ?_, hc2⟩
      rw [List.getLast?_append] at hl
      simpa [List.getLast?_cons] using hl
    have e := G.wlen_append_cons A u (v :: B)
    rw [G.wlen_cons_cons] at e
    have a1 := G.dist_le_wlen w1
    have a2 := G.dist_le_wlen w2
    obtain ⟨hsu, _⟩ : G.Reach (G.s i) u ∧ True := ⟨⟨_, w1⟩, trivial⟩
    have hvt : G.Reach v (G.t i) := ⟨_, w2⟩
    refine ⟨huv, hsu, hvt, ?_⟩
    obtain ⟨hut, b2⟩ := G.dist_le_len_add_dist hvt huv
    have b1 := (G.dist_triangle hsu hut).2
    rw [hd]
    linarith
  · intro hc
    refine ⟨h, ?_⟩
    obtain ⟨⟨hh, hl, _⟩, _⟩ := h
    obtain ⟨x, rest, rfl⟩ : ∃ x rest, R = x :: rest := by
      cases R with
      | nil => simp at hh
      | cons x rest => exact ⟨x, rest, rfl⟩
    have hx : x = G.s i := by simpa using hh
    subst hx
    rw [G.wlen_of_chain_inD i rest _ (G.t i) hc hl, G.dist_self]
    simp

/-- lem:Di (c).  `D_i` is acyclic. -/
theorem lem_Di_c (i : Fin k) (u : V) : ¬ Relation.TransGen (G.inD i) u u := by
  have key : ∀ a b, Relation.TransGen (G.inD i) a b → G.dist (G.s i) a < G.dist (G.s i) b := by
    intro a b hab
    induction hab with
    | single h =>
      have := (G.lem_Di_a h).2.1
      have := G.len_pos _ _ h.1
      linarith
    | tail _ h ih =>
      have := (G.lem_Di_a h).2.1
      have := G.len_pos _ _ h.1
      linarith
  intro h
  exact lt_irrefl _ (key u u h)

end Instance

end DSPP
