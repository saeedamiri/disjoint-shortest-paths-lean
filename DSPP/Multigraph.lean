/-
Multigraphs: directed and undirected graphs with parallel arcs or edges, their paths, and the
vertex-, arc- and edge-disjoint versions of the problem.

Paper: "Directed k Disjoint Shortest Paths Is Polynomial for Every Fixed k" (Saeed Amiri),
Section "Introduction" (the arc- and edge-disjoint versions), Section "Preliminaries" (paths),
and Section "Remarks and open problems".

A multigraph has a vertex type `V` and an edge type `E`.  Directed and undirected multigraphs are
both given by a step relation: `step u e w` says that the arc or edge `e` leads from `u` to `w`.
A walk from `a` is a list of steps `(e, w)`: traverse `e` and arrive at `w`.  So a walk records
its arcs or edges, and parallel arcs or edges are told apart.  A path is a walk whose vertices are
pairwise distinct, as in the paper.
-/
import DSPP.Basic

open Classical

namespace DSPP

/-- A multigraph with positive lengths on its arcs or edges.  `step u e w`: the arc or edge `e`
leads from `u` to `w`.  `step_end`: if `e` leads from `a` and also from `u` to `w`, then `a` is
one of `u`, `w` (an arc or edge has at most two ends). -/
structure MGraph (V E : Type*) where
  /-- `step u e w`: the arc or edge `e` leads from `u` to `w`. -/
  step : V → E → V → Prop
  /-- The length of an arc or edge. -/
  len : E → ℝ
  /-- Lengths are positive. -/
  len_pos : ∀ e, 0 < len e
  /-- An arc or edge has at most two ends. -/
  step_end : ∀ {a v u w : V} {e : E}, step a e v → step u e w → a = u ∨ a = w

namespace MGraph

variable {V E : Type*}

/-- The vertices of a walk from `a`, in order. -/
def verts (a : V) (W : List (E × V)) : List V := a :: W.map Prod.snd

/-- The arcs or edges of a walk, in order. -/
def edges (W : List (E × V)) : List E := W.map Prod.fst

variable (M : MGraph V E)

/-- `W` is a walk from `a` to `b`. -/
def IsWalk : V → List (E × V) → V → Prop
  | a, [], b => a = b
  | a, x :: W, b => M.step a x.1 x.2 ∧ IsWalk x.2 W b

/-- `W` is a path from `a` to `b`: a walk whose vertices are pairwise distinct. -/
def IsPath (a : V) (W : List (E × V)) (b : V) : Prop :=
  M.IsWalk a W b ∧ (verts a W).Nodup

/-- The length of a walk. -/
noncomputable def mlen (W : List (E × V)) : ℝ := (W.map fun x => M.len x.1).sum

/-- A shortest path from `a` to `b`: a path not longer than any other path from `a` to `b`. -/
def IsShortestPath (a : V) (W : List (E × V)) (b : V) : Prop :=
  M.IsPath a W b ∧ ∀ W', M.IsPath a W' b → M.mlen W ≤ M.mlen W'

variable {k : ℕ}

/-- A solution of the arc- or edge-disjoint version: `P i` is a shortest `s_i`--`t_i` path, and
the paths are pairwise arc- or edge-disjoint. -/
def IsEdgeSolution (s t : Fin k → V) (P : Fin k → List (E × V)) : Prop :=
  (∀ i, M.IsShortestPath (s i) (P i) (t i)) ∧
    ∀ i j, i ≠ j → ∀ e ∈ edges (P i), e ∉ edges (P j)

/-- The arc- or edge-disjoint version has a solution. -/
def HasEdgeSolution (s t : Fin k → V) : Prop := ∃ P, M.IsEdgeSolution s t P

/-- A solution of the vertex-disjoint version: `P i` is a shortest `s_i`--`t_i` path, and the
paths are pairwise vertex-disjoint. -/
def IsVertexSolution (s t : Fin k → V) (P : Fin k → List (E × V)) : Prop :=
  (∀ i, M.IsShortestPath (s i) (P i) (t i)) ∧
    ∀ i j, i ≠ j → ∀ v ∈ verts (s i) (P i), v ∉ verts (s j) (P j)

/-- The vertex-disjoint version has a solution. -/
def HasVertexSolution (s t : Fin k → V) : Prop := ∃ P, M.IsVertexSolution s t P

/-! ### Directed and undirected multigraphs -/

/-- A directed multigraph: arc `e` leads from `src e` to `tgt e`. -/
def ofArcs (src tgt : E → V) (len : E → ℝ) (len_pos : ∀ e, 0 < len e) : MGraph V E where
  step u e w := src e = u ∧ tgt e = w
  len := len
  len_pos := len_pos
  step_end := by
    rintro a v u w e ⟨rfl, -⟩ ⟨h, -⟩
    exact Or.inl h

/-- An undirected multigraph: edge `e` joins `fst e` and `snd e` and can be traversed both
ways. -/
def ofEdges (fst snd : E → V) (len : E → ℝ) (len_pos : ∀ e, 0 < len e) : MGraph V E where
  step u e w := (fst e = u ∧ snd e = w) ∨ (fst e = w ∧ snd e = u)
  len := len
  len_pos := len_pos
  step_end := by
    rintro a v u w e h1 h2
    rcases h1 with ⟨rfl, -⟩ | ⟨-, rfl⟩ <;> rcases h2 with ⟨h, h'⟩ | ⟨h, h'⟩ <;> simp_all

/-- The sub-multigraph on the arcs or edges satisfying `p`. -/
def restrict (p : E → Prop) : MGraph V {e // p e} where
  step u e w := M.step u e.1 w
  len e := M.len e.1
  len_pos e := M.len_pos e.1
  step_end h1 h2 := M.step_end h1 h2

/-! ### Walks -/

@[simp] theorem verts_nil (a : V) : verts a ([] : List (E × V)) = [a] := rfl

@[simp] theorem verts_cons (a : V) (x : E × V) (W : List (E × V)) :
    verts a (x :: W) = a :: verts x.2 W := rfl

@[simp] theorem edges_nil : edges ([] : List (E × V)) = [] := rfl

@[simp] theorem edges_cons (x : E × V) (W : List (E × V)) :
    edges (x :: W) = x.1 :: edges W := rfl

@[simp] theorem isWalk_nil {a b : V} : M.IsWalk a [] b ↔ a = b := Iff.rfl

@[simp] theorem isWalk_cons {a b : V} {x : E × V} {W : List (E × V)} :
    M.IsWalk a (x :: W) b ↔ M.step a x.1 x.2 ∧ M.IsWalk x.2 W b := Iff.rfl

@[simp] theorem mlen_nil : M.mlen ([] : List (E × V)) = 0 := by simp [mlen]

@[simp] theorem mlen_cons (x : E × V) (W : List (E × V)) :
    M.mlen (x :: W) = M.len x.1 + M.mlen W := by simp [mlen]

theorem mlen_append (A B : List (E × V)) : M.mlen (A ++ B) = M.mlen A + M.mlen B := by
  simp [mlen]

theorem mlen_nonneg (W : List (E × V)) : 0 ≤ M.mlen W :=
  List.sum_nonneg (by simp only [List.mem_map]; rintro _ ⟨x, -, rfl⟩; exact (M.len_pos _).le)

theorem mlen_le_of_sublist {A B : List (E × V)} (h : A.Sublist B) : M.mlen A ≤ M.mlen B :=
  (h.map _).sum_le_sum
    (by simp only [List.mem_map]; rintro _ ⟨x, -, rfl⟩; exact (M.len_pos _).le)

theorem isWalk_append {a b c : V} {A B : List (E × V)} (hA : M.IsWalk a A b)
    (hB : M.IsWalk b B c) : M.IsWalk a (A ++ B) c := by
  induction A generalizing a with
  | nil => simp only [isWalk_nil] at hA; subst hA; simpa using hB
  | cons x A ih => exact ⟨hA.1, ih hA.2⟩

theorem isWalk_of_append_cons {a b : V} {A B : List (E × V)} {x : E × V}
    (h : M.IsWalk a (A ++ x :: B) b) : M.IsWalk x.2 B b := by
  induction A generalizing a with
  | nil => exact h.2
  | cons y A ih => exact ih h.2

/-- The last vertex of a non-empty walk is its end. -/
theorem end_mem_snd {a b : V} {W : List (E × V)} (h : M.IsWalk a W b) (hW : W ≠ []) :
    b ∈ W.map Prod.snd := by
  induction W generalizing a with
  | nil => exact absurd rfl hW
  | cons x W ih =>
    by_cases hW' : W = []
    · subst hW'
      have := h.2
      simp only [isWalk_nil] at this
      simp [this]
    · exact List.mem_cons_of_mem _ (ih h.2 hW')

/-- Every step of a walk joins two vertices of the walk. -/
theorem step_of_mem {a b : V} {W : List (E × V)} (h : M.IsWalk a W b) {x : E × V}
    (hx : x ∈ W) : ∃ u ∈ verts a W, M.step u x.1 x.2 ∧ x.2 ∈ verts a W := by
  induction W generalizing a with
  | nil => simp at hx
  | cons y W ih =>
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨a, by simp, h.1, by simp [verts]⟩
    · obtain ⟨u, hu, hs, hw⟩ := ih h.2 hx
      exact ⟨u, List.mem_cons_of_mem _ hu, hs, List.mem_cons_of_mem _ hw⟩

/-- A path from `a` to `a` is the one-vertex path. -/
theorem eq_nil_of_isPath_self {a : V} {W : List (E × V)} (h : M.IsPath a W a) : W = [] := by
  by_contra hW
  have := M.end_mem_snd h.1 hW
  exact (List.nodup_cons.1 h.2).1 this

/-- A path from `a` to `b ≠ a` is not empty. -/
theorem ne_nil_of_isPath {a b : V} {W : List (E × V)} (h : M.IsPath a W b) (hab : a ≠ b) :
    W ≠ [] := by
  rintro rfl
  exact hab h.1

theorem isPath_tail {a b : V} {x : E × V} {W : List (E × V)} (h : M.IsPath a (x :: W) b) :
    M.IsPath x.2 W b :=
  ⟨h.1.2, (List.nodup_cons.1 h.2).2⟩

/-- Shortcutting: every walk contains a path with the same ends, as a sublist. -/
theorem exists_path_sublist {a b : V} {W : List (E × V)} (h : M.IsWalk a W b) :
    ∃ P, M.IsPath a P b ∧ P.Sublist W := by
  induction W generalizing a with
  | nil =>
    simp only [isWalk_nil] at h
    subst h
    exact ⟨[], ⟨rfl, by simp⟩, List.Sublist.slnil⟩
  | cons x W ih =>
    obtain ⟨P', hP', hsub⟩ := ih h.2
    by_cases hax : a = x.2
    · subst hax
      exact ⟨P', hP', hsub.cons x⟩
    by_cases ha : a ∈ P'.map Prod.snd
    · obtain ⟨y, hy, hya⟩ := List.mem_map.1 ha
      obtain ⟨A, B, rfl⟩ := List.append_of_mem hy
      have hw := M.isWalk_of_append_cons hP'.1
      rw [hya] at hw
      refine ⟨B, ⟨hw, ?_⟩, ?_⟩
      · have hnd := hP'.2
        simp only [verts, List.map_append, List.map_cons, hya] at hnd
        exact hnd.sublist ((List.sublist_append_right _ _).cons _)
      · exact (((List.sublist_cons_self y B).trans (List.sublist_append_right A _)).trans
          hsub).cons x
    · refine ⟨x :: P', ⟨⟨h.1, hP'.1⟩, ?_⟩, hsub.cons₂ x⟩
      rw [verts_cons, List.nodup_cons]
      refine ⟨?_, hP'.2⟩
      simp only [verts, List.mem_cons]
      rintro (h' | h')
      · exact hax h'
      · exact ha h'

/-- Shortcutting, with lengths: every walk contains a path with the same ends whose arcs or
edges are among those of the walk and which is not longer. -/
theorem exists_path_of_walk {a b : V} {W : List (E × V)} (h : M.IsWalk a W b) :
    ∃ P, M.IsPath a P b ∧ (∀ e ∈ edges P, e ∈ edges W) ∧ M.mlen P ≤ M.mlen W := by
  obtain ⟨P, hP, hsub⟩ := M.exists_path_sublist h
  exact ⟨P, hP, fun e he => (hsub.map Prod.fst).subset he, M.mlen_le_of_sublist hsub⟩

/-- In a path, the arcs or edges have pairwise distinct values under `g`, if two arcs or edges
with the same value of `g` that leave `a` and `u` have `a` as an end of the second one. -/
theorem nodup_map_of_isPath {P : Type*} (g : E → P)
    (hg : ∀ {a v u w : V} {e f : E}, M.step a e v → M.step u f w → g e = g f → a = u ∨ a = w)
    {a b : V} {W : List (E × V)} (h : M.IsPath a W b) : ((edges W).map g).Nodup := by
  induction W generalizing a with
  | nil => simp
  | cons x W ih =>
    have ht := M.isPath_tail h
    simp only [edges_cons, List.map_cons, List.nodup_cons]
    refine ⟨?_, ih ht⟩
    intro hx
    obtain ⟨f, hf, hfg⟩ := List.mem_map.1 hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hf
    obtain ⟨u, hu, hs, hw⟩ := M.step_of_mem ht.1 hy
    have hna : a ∉ verts x.2 W := (List.nodup_cons.1 h.2).1
    rcases hg h.1.1 hs hfg.symm with rfl | rfl
    · exact hna hu
    · exact hna hw

/-- The arcs or edges of a path are pairwise distinct. -/
theorem nodup_edges {a b : V} {W : List (E × V)} (h : M.IsPath a W b) : (edges W).Nodup := by
  simpa using M.nodup_map_of_isPath id (fun h1 h2 he => by
    simp only [id] at he; subst he; exact M.step_end h1 h2) h

/-! ### Replacing arcs or edges -/

/-- Replacing the arc or edge of every step by one that makes the same step. -/
theorem isWalk_map {E' : Type*} (M' : MGraph V E') (φ : E → E') {a b : V} {W : List (E × V)}
    (hφ : ∀ x ∈ W, ∀ u, M.step u x.1 x.2 → M'.step u (φ x.1) x.2) (h : M.IsWalk a W b) :
    M'.IsWalk a (W.map (Prod.map φ id)) b := by
  induction W generalizing a with
  | nil => exact h
  | cons x W ih =>
    exact ⟨hφ x (by simp) a h.1, ih (fun y hy => hφ y (List.mem_cons_of_mem _ hy)) h.2⟩

@[simp] theorem verts_map {E' : Type*} (φ : E → E') (a : V) (W : List (E × V)) :
    verts a (W.map (Prod.map φ id)) = verts a W := by
  simp [verts, Function.comp_def]

theorem edges_map {E' : Type*} (φ : E → E') (W : List (E × V)) :
    edges (W.map (Prod.map φ id)) = (edges W).map φ := by
  simp [edges, Function.comp_def]

theorem isPath_map {E' : Type*} (M' : MGraph V E') (φ : E → E') {a b : V} {W : List (E × V)}
    (hφ : ∀ x ∈ W, ∀ u, M.step u x.1 x.2 → M'.step u (φ x.1) x.2) (h : M.IsPath a W b) :
    M'.IsPath a (W.map (Prod.map φ id)) b :=
  ⟨M.isWalk_map M' φ hφ h.1, by rw [verts_map]; exact h.2⟩

theorem mlen_map_le {E' : Type*} (M' : MGraph V E') (φ : E → E') {W : List (E × V)}
    (hφ : ∀ x ∈ W, M'.len (φ x.1) ≤ M.len x.1) :
    M'.mlen (W.map (Prod.map φ id)) ≤ M.mlen W := by
  induction W with
  | nil => simp
  | cons x W ih =>
    simp only [List.map_cons, mlen_cons, Prod.map_fst]
    exact add_le_add (hφ x (by simp)) (ih fun y hy => hφ y (List.mem_cons_of_mem _ hy))

theorem mlen_map_eq {E' : Type*} (M' : MGraph V E') (φ : E → E') {W : List (E × V)}
    (hφ : ∀ x ∈ W, M'.len (φ x.1) = M.len x.1) :
    M'.mlen (W.map (Prod.map φ id)) = M.mlen W := by
  induction W with
  | nil => simp
  | cons x W ih =>
    simp only [List.map_cons, mlen_cons, Prod.map_fst]
    rw [hφ x (by simp), ih fun y hy => hφ y (List.mem_cons_of_mem _ hy)]

/-- Paths of a sub-multigraph are paths of the multigraph, with the same length. -/
theorem isPath_restrict {p : E → Prop} {a b : V} {W : List ({e // p e} × V)}
    (h : (M.restrict p).IsPath a W b) : M.IsPath a (W.map (Prod.map Subtype.val id)) b :=
  (M.restrict p).isPath_map M Subtype.val (fun _ _ _ h => h) h

theorem mlen_restrict {p : E → Prop} (W : List ({e // p e} × V)) :
    M.mlen (W.map (Prod.map Subtype.val id)) = (M.restrict p).mlen W :=
  (M.restrict p).mlen_map_eq M Subtype.val (fun _ _ => rfl)

/-- A path of `M` all of whose arcs or edges satisfy `p` is a path of `M.restrict p`. -/
theorem exists_restrict {p : E → Prop} {a b : V} {W : List (E × V)} (h : M.IsWalk a W b)
    (hp : ∀ e ∈ edges W, p e) :
    ∃ W' : List ({e // p e} × V), (M.restrict p).IsWalk a W' b ∧
      W'.map (Prod.map Subtype.val id) = W := by
  induction W generalizing a with
  | nil => exact ⟨[], h, rfl⟩
  | cons x W ih =>
    obtain ⟨W', hW', rfl⟩ := ih h.2 (fun e he => hp e (List.mem_cons_of_mem _ he))
    exact ⟨(⟨x.1, hp x.1 (by simp)⟩, x.2) :: W', ⟨h.1, hW'⟩, rfl⟩

/-! ### Arcs or edges along a walk -/

theorem isChain_edges (R : E → E → Prop)
    (hR : ∀ {u x w : V} {e f : E}, M.step u e x → M.step x f w → R e f)
    {a b : V} {W : List (E × V)} (h : M.IsWalk a W b) : (edges W).IsChain R := by
  induction W generalizing a with
  | nil => simp
  | cons x W ih =>
    cases W with
    | nil => simp
    | cons y W =>
      simp only [edges_cons] at ih ⊢
      exact List.isChain_cons_cons.2 ⟨hR h.1 h.2.1, ih h.2⟩

theorem head_step {a b : V} {W : List (E × V)} (h : M.IsWalk a W b) :
    ∀ e ∈ (edges W).head?, ∃ v, M.step a e v := by
  cases W with
  | nil => simp
  | cons x W => intro e he; simp only [edges_cons, List.head?_cons, Option.mem_def,
      Option.some.injEq] at he; subst he; exact ⟨_, h.1⟩

theorem last_step {a b : V} {W : List (E × V)} (h : M.IsWalk a W b) :
    ∀ e ∈ (edges W).getLast?, ∃ u, M.step u e b := by
  induction W generalizing a with
  | nil => simp
  | cons x W ih =>
    cases W with
    | nil =>
      intro e he
      simp only [edges_cons, edges_nil, List.getLast?_singleton, Option.mem_def,
        Option.some.injEq] at he
      subst he
      have h2 := h.2
      simp only [isWalk_nil] at h2
      exact ⟨a, h2 ▸ h.1⟩
    | cons y W =>
      intro e he
      simp only [edges_cons, List.getLast?_cons_cons] at he
      exact ih h.2 e (by simpa using he)

theorem isChain_ne_of_nodup {α : Type*} {R : α → α → Prop} :
    ∀ {l : List α}, l.Nodup → l.IsChain R → l.IsChain (fun a b => a ≠ b ∧ R a b)
  | [], _, _ => by simp
  | [_], _, _ => by simp
  | a :: b :: l, hn, hc => by
    rw [List.isChain_cons_cons] at hc ⊢
    refine ⟨⟨fun h => (List.nodup_cons.1 hn).1 (h ▸ List.mem_cons_self ..), hc.1⟩, ?_⟩
    exact isChain_ne_of_nodup (List.nodup_cons.1 hn).2 hc.2

/-- In a path, every step joins two distinct vertices. -/
theorem step_ne_of_isPath {a b : V} {W : List (E × V)} (h : M.IsPath a W b) {x : E × V}
    (hx : x ∈ W) : ∃ u, M.step u x.1 x.2 ∧ u ≠ x.2 := by
  induction W generalizing a with
  | nil => simp at hx
  | cons y W ih =>
    rcases List.mem_cons.1 hx with rfl | hx
    · refine ⟨a, h.1.1, fun he => (List.nodup_cons.1 h.2).1 ?_⟩
      rw [he]; simp
    · exact ih (M.isPath_tail h) hx

theorem mlen_eq_sum (W : List (E × V)) : M.mlen W = ((edges W).map M.len).sum := by
  simp [mlen, edges, Function.comp_def]

end MGraph

end DSPP
