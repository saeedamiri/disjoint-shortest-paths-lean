/-
Routes through prescribed vertices (cor:waypoints).

Paper: "Directed k Disjoint Shortest Paths Is Polynomial for Every Fixed k" (Saeed Amiri),
Section "Remarks", paragraph "Routes through prescribed vertices" and cor:waypoints.

A route through `w 0, …, w ℓ` in this order is given by its segments: `R i` is the part of the
route from `w i` to `w (i+1)`, and the route is the concatenation `catW R`.  Its length is at
least `wayLen w = ∑ dist (w i) (w (i+1))` (`wayLen_le`).  The three kinds of route of
cor:waypoints are
* (i) `IsPathRoute`: the route is a path;
* (ii) `IsCycleRoute`: `w ℓ = w 0` and the vertices of the closed route are pairwise distinct;
* (iii) `IsTrailRoute`: the route uses every arc or edge at most once.
For (iii), a route of length `wayLen w` is the same as pairwise arc- or edge-disjoint shortest
paths for the pairs `(w i, w (i+1))` (`trail_iff`), and cor:edgedisjoint decides this.  For (i)
and (ii), the graph `G'` (`splitG`) splits every `v` in a set `W` into `v⁻ = inl v`, which
receives the arcs into `v`, and `v⁺ = inr v`, which sends the arcs out of `v`.  An undirected
graph enters through its two orientations of every edge (an arc presentation `σ τ π ρ`).  A
route of length `wayLen w` exists iff the distance check `splitCheck` passes and `G'` has
vertex-disjoint shortest paths (`vroute_iff`), and thm:main decides the latter.
-/
import DSPP.ParallelArcs
import DSPP.EdgeDisjointCor

open Classical

namespace DSPP

namespace MGraph

variable {V E : Type*} (M : MGraph V E) {ℓ : ℕ}

/-! ### Routes and their length -/

/-- The walk made of the segments `R 0, …, R (ℓ-1)` in this order. -/
def catW (R : Fin ℓ → List (E × V)) : List (E × V) := (List.ofFn R).flatten

/-- `R i` is a walk from `w i` to `w (i+1)` for every `i < ℓ`: the route `catW R` goes from
`w 0` to `w ℓ` through `w 1, …, w (ℓ-1)` in this order, and `R i` is its part between the
visits of `w i` and `w (i+1)`. -/
def IsSegs (w : Fin (ℓ + 1) → V) (R : Fin ℓ → List (E × V)) : Prop :=
  ∀ i : Fin ℓ, M.IsWalk (w i.castSucc) (R i) (w i.succ)

/-- Kind (i): a path from `w 0` to `w ℓ` through `w 1, …, w (ℓ-1)` in this order. -/
def IsPathRoute (w : Fin (ℓ + 1) → V) (R : Fin ℓ → List (E × V)) : Prop :=
  M.IsSegs w R ∧ (verts (w 0) (catW R)).Nodup

/-- Kind (ii): a closed walk through `w 0, …, w (ℓ-1)` in this cyclic order (`w ℓ = w 0`)
whose vertices are pairwise distinct: a cycle (for an undirected graph when `ℓ ≥ 3`). -/
def IsCycleRoute (w : Fin (ℓ + 1) → V) (R : Fin ℓ → List (E × V)) : Prop :=
  M.IsSegs w R ∧ w (Fin.last ℓ) = w 0 ∧ ((catW R).map Prod.snd).Nodup

/-- Kind (iii): a walk from `w 0` to `w ℓ` through `w 1, …, w (ℓ-1)` in this order that uses
every arc or edge at most once. -/
def IsTrailRoute (w : Fin (ℓ + 1) → V) (R : Fin ℓ → List (E × V)) : Prop :=
  M.IsSegs w R ∧ (edges (catW R)).Nodup

theorem catW_zero (R : Fin 0 → List (E × V)) : catW R = [] := rfl

theorem catW_succ {n : ℕ} (R : Fin (n + 1) → List (E × V)) :
    catW R = R 0 ++ catW fun i : Fin n => R i.succ := by
  simp [catW, List.ofFn_succ]

/-- The segments make one walk from `w 0` to `w ℓ`. -/
theorem isWalk_catW : ∀ {n : ℕ} (w : Fin (n + 1) → V) (R : Fin n → List (E × V)),
    M.IsSegs w R → M.IsWalk (w 0) (catW R) (w (Fin.last n))
  | 0, w, R, _ => by rw [catW_zero]; rfl
  | n + 1, w, R, h => by
    rw [catW_succ]
    refine M.isWalk_append (h 0) ?_
    have := isWalk_catW (fun i : Fin (n + 1) => w i.succ) (fun i => R i.succ)
      (fun i => by
        have e : (i.castSucc.succ : Fin (n + 2)) = i.succ.castSucc := Fin.ext (by simp)
        show M.IsWalk (w i.castSucc.succ) _ _
        rw [e]; exact h i.succ)
    simpa only [Fin.succ_last] using this

theorem mlen_catW : ∀ {n : ℕ} (R : Fin n → List (E × V)),
    M.mlen (catW R) = ∑ i, M.mlen (R i)
  | 0, R => by simp [catW_zero]
  | n + 1, R => by rw [catW_succ, M.mlen_append, mlen_catW, Fin.sum_univ_succ]

theorem map_snd_catW {n : ℕ} (R : Fin n → List (E × V)) :
    (catW R).map Prod.snd = (List.ofFn fun i => (R i).map Prod.snd).flatten := by
  simp [catW, List.map_flatten, List.map_ofFn, Function.comp_def]

theorem edges_catW {n : ℕ} (R : Fin n → List (E × V)) :
    edges (catW R) = (List.ofFn fun i => edges (R i)).flatten := by
  simp [catW, edges, List.map_flatten, List.map_ofFn, Function.comp_def]

theorem nodup_flatten_ofFn {α : Type*} {n : ℕ} (f : Fin n → List α) :
    (List.ofFn f).flatten.Nodup ↔ (∀ i, (f i).Nodup) ∧ ∀ i j, i ≠ j → ∀ a ∈ f i, a ∉ f j := by
  rw [List.nodup_flatten, List.pairwise_ofFn]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => h1 _ (by simp), fun i j hij a ha ha' => ?_⟩
    rcases lt_or_gt_of_ne hij with h | h
    · exact h2 h ha ha'
    · exact h2 h ha' ha
  · rintro ⟨h1, h2⟩
    refine ⟨fun l hl => ?_, fun i j hij a ha ha' => h2 i j (ne_of_lt hij) a ha ha'⟩
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hl
    exact h1 i

theorem mem_flatten_ofFn {α : Type*} {n : ℕ} (f : Fin n → List α) {a : α} :
    a ∈ (List.ofFn f).flatten ↔ ∃ i, a ∈ f i := by
  simp [List.mem_flatten, List.mem_ofFn]

/-- The distance from `a` to `b`: the infimum of the lengths of the paths from `a` to `b`
(`0` by convention if there is none). -/
noncomputable def dist (a b : V) : ℝ := sInf {x | ∃ P, M.IsPath a P b ∧ M.mlen P = x}

theorem dist_le_path {a b : V} {P : List (E × V)} (h : M.IsPath a P b) :
    M.dist a b ≤ M.mlen P :=
  csInf_le ⟨0, by rintro _ ⟨Q, -, rfl⟩; exact M.mlen_nonneg Q⟩ ⟨P, h, rfl⟩

theorem dist_le_walk {a b : V} {W : List (E × V)} (h : M.IsWalk a W b) :
    M.dist a b ≤ M.mlen W := by
  obtain ⟨P, hP, -, hl⟩ := M.exists_path_of_walk h
  exact (M.dist_le_path hP).trans hl

theorem dist_eq {a b : V} {P : List (E × V)} (h : M.IsShortestPath a P b) :
    M.dist a b = M.mlen P :=
  (show IsLeast {x | ∃ P, M.IsPath a P b ∧ M.mlen P = x} (M.mlen P) from
    ⟨⟨P, h.1, rfl⟩, by rintro _ ⟨Q, hQ, rfl⟩; exact h.2 Q hQ⟩).csInf_eq

theorem isShortestPath_of {a b : V} {P : List (E × V)} (h : M.IsPath a P b)
    (hl : M.mlen P ≤ M.dist a b) : M.IsShortestPath a P b :=
  ⟨h, fun _ hQ => hl.trans (M.dist_le_path hQ)⟩

/-- The lower bound `L = ∑ dist (w i) (w (i+1))` of cor:waypoints. -/
noncomputable def wayLen (w : Fin (ℓ + 1) → V) : ℝ :=
  ∑ i : Fin ℓ, M.dist (w i.castSucc) (w i.succ)

/-- cor:waypoints, the lower bound: every route through `w 0, …, w ℓ` in this order, of any
kind, has length at least `L`. -/
theorem wayLen_le {w : Fin (ℓ + 1) → V} {R : Fin ℓ → List (E × V)} (h : M.IsSegs w R) :
    M.wayLen w ≤ M.mlen (catW R) := by
  rw [mlen_catW]
  exact Finset.sum_le_sum fun i _ => M.dist_le_walk (h i)

/-- A route of length `L`: every segment has the length of a shortest path. -/
theorem segs_eq {w : Fin (ℓ + 1) → V} {R : Fin ℓ → List (E × V)} (h : M.IsSegs w R)
    (hL : M.mlen (catW R) = M.wayLen w) (i : Fin ℓ) :
    M.mlen (R i) = M.dist (w i.castSucc) (w i.succ) := by
  rw [mlen_catW, wayLen] at hL
  exact ((Finset.sum_eq_sum_iff_of_le fun j _ => M.dist_le_walk (h j)).1 hL.symm i
    (Finset.mem_univ _)).symm

/-! ### Kind (iii): arc- or edge-disjoint shortest paths -/

/-- cor:waypoints (iii), the reduction: a route of kind (iii) of length `L` exists iff there
are pairwise arc- or edge-disjoint shortest paths for the pairs `(w i, w (i+1))`. -/
theorem trail_iff (w : Fin (ℓ + 1) → V) :
    (∃ R, M.IsTrailRoute w R ∧ M.mlen (catW R) = M.wayLen w) ↔
      M.HasEdgeSolution (fun i : Fin ℓ => w i.castSucc) (fun i => w i.succ) := by
  constructor
  · rintro ⟨R, ⟨hs, hnd⟩, hL⟩
    have heq := M.segs_eq hs hL
    choose P hP hsub hle using fun i => M.exists_path_of_walk (hs i)
    rw [edges_catW, nodup_flatten_ofFn] at hnd
    exact ⟨P, fun i => M.isShortestPath_of (hP i) ((hle i).trans (heq i).le),
      fun i j hij e he he' => hnd.2 i j hij e (hsub i e he) (hsub j e he')⟩
  · rintro ⟨P, hP, hdis⟩
    refine ⟨P, ⟨fun i => (hP i).1.1, ?_⟩, ?_⟩
    · rw [edges_catW, nodup_flatten_ofFn]
      exact ⟨fun i => M.nodup_edges (hP i).1, hdis⟩
    · rw [mlen_catW, wayLen]
      exact Finset.sum_congr rfl fun i _ => (M.dist_eq (hP i)).symm

/-! ### Kinds (i) and (ii): splitting the prescribed vertices -/

section Split

variable [DecidableEq V] {E' : Type*} (σ τ : E' → V) (π : E' → E) (ρ : V → E → V → E')
variable (Wset : Finset V)

/-- `v⁺`: the copy of `v` that sends the arcs out of `v` (`inr v` if `v` is split). -/
def plus (v : V) : V ⊕ V := if v ∈ Wset then Sum.inr v else Sum.inl v

/-- The projection of `G'` onto `G`. -/
def proj : V ⊕ V → V := Sum.elim id id

@[simp] theorem proj_plus (v : V) : proj (plus Wset v) = v := by
  unfold plus; split_ifs <;> rfl

omit [DecidableEq V] in
@[simp] theorem proj_inl (v : V) : proj (Sum.inl v : V ⊕ V) = v := rfl

theorem plus_eq_inl {v u : V} (h : plus Wset v = Sum.inl u) : v ∉ Wset ∧ v = u := by
  unfold plus at h
  by_cases hv : v ∈ Wset
  · rw [if_pos hv] at h; exact absurd h (by simp)
  · rw [if_neg hv] at h; exact ⟨hv, Sum.inl_injective h⟩

theorem plus_of_not_mem {v : V} (h : v ∉ Wset) : plus Wset v = Sum.inl v := by
  simp [plus, h]

/-- The graph `G'`: the arc `x` of the arc presentation (an arc of a digraph, or one
orientation of an edge) leads from `(σ x)⁺` to `(τ x)⁻ = inl (τ x)`. -/
noncomputable def splitG : MGraph (V ⊕ V) E' :=
  ofArcs (fun x => plus Wset (σ x)) (fun x => Sum.inl (τ x)) (fun x => M.len (π x))
    (fun x => M.len_pos (π x))

/-- The distance check of the proof of cor:waypoints:
`dist' (w i⁺) (w (i+1)⁻) ≤ dist (w i) (w (i+1))` for every `i`. -/
def splitCheck (w : Fin (ℓ + 1) → V) : Prop :=
  ∀ i : Fin ℓ, (M.splitG σ τ π Wset).dist (plus Wset (w i.castSucc)) (Sum.inl (w i.succ)) ≤
    M.dist (w i.castSucc) (w i.succ)

/-- A walk of `G'` read in `G`. -/
def projW (P : List (E' × (V ⊕ V))) : List (E × V) := P.map fun y => (π y.1, proj y.2)

/-- A walk of `G` lifted to `G'`. -/
def liftW : V → List (E × V) → List (E' × (V ⊕ V))
  | _, [] => []
  | u, x :: W => (ρ u x.1 x.2, Sum.inl x.2) :: liftW x.2 W

variable {σ τ π ρ Wset}

theorem snd_mem_splitG {x : V ⊕ V} {P : List (E' × (V ⊕ V))} {y : V ⊕ V}
    (h : (M.splitG σ τ π Wset).IsWalk x P y) {z : E' × (V ⊕ V)} (hz : z ∈ P) :
    z.2 = Sum.inl (τ z.1) := by
  obtain ⟨u, -, hs, -⟩ := (M.splitG σ τ π Wset).step_of_mem h hz
  exact hs.2.symm

theorem isWalk_projW (hσ : ∀ x, M.step (σ x) (π x) (τ x)) :
    ∀ {x y : V ⊕ V} {P : List (E' × (V ⊕ V))}, (M.splitG σ τ π Wset).IsWalk x P y →
      M.IsWalk (proj x) (projW π P) (proj y)
  | x, y, [], h => by
    have : x = y := h
    subst this; rfl
  | x, y, z :: P, h => by
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    have h1' : plus Wset (σ z.1) = x := h1
    have h2' : Sum.inl (τ z.1) = z.2 := h2
    refine ⟨?_, isWalk_projW hσ h3⟩
    show M.step (proj x) (π z.1) (proj z.2)
    rw [← h1', ← h2']
    simpa using hσ z.1

theorem mlen_projW (P : List (E' × (V ⊕ V))) :
    M.mlen (projW π P) = (M.splitG σ τ π Wset).mlen P := by
  induction P with
  | nil => simp [projW]
  | cons z P ih =>
    simp only [projW, List.map_cons, mlen_cons] at ih ⊢
    rw [ih]; rfl

theorem map_snd_projW (P : List (E' × (V ⊕ V))) :
    (projW π P).map Prod.snd = (P.map Prod.snd).map proj := by
  simp [projW, Function.comp_def]

theorem map_snd_liftW : ∀ (u : V) (W : List (E × V)),
    (liftW ρ u W).map Prod.snd = (W.map Prod.snd).map Sum.inl
  | _, [] => rfl
  | u, x :: W => by simp [liftW, map_snd_liftW x.2 W]

variable (hρ : ∀ u e v, M.step u e v → σ (ρ u e v) = u ∧ τ (ρ u e v) = v ∧ π (ρ u e v) = e)
include hρ

theorem mlen_liftW : ∀ {u v : V} {W : List (E × V)}, M.IsWalk u W v →
    (M.splitG σ τ π Wset).mlen (liftW ρ u W) = M.mlen W
  | _, _, [], _ => by simp [liftW]
  | u, v, x :: W, h => by
    simp only [liftW, mlen_cons]
    rw [mlen_liftW h.2]
    show M.len (π (ρ u x.1 x.2)) + M.mlen W = _
    rw [(hρ _ _ _ h.1).2.2]

theorem isWalk_liftW : ∀ {u v : V} {W : List (E × V)}, M.IsPath u W v →
    (∀ x ∈ W, x.2 ≠ v → x.2 ∉ Wset) → W ≠ [] →
    (M.splitG σ τ π Wset).IsWalk (plus Wset u) (liftW ρ u W) (Sum.inl v)
  | _, _, [], _, _, hne => absurd rfl hne
  | u, v, x :: W, h, hin, _ => by
    obtain ⟨h1, h2, -⟩ := hρ _ _ _ h.1.1
    refine ⟨⟨by simp [h1], by simp [h2]⟩, ?_⟩
    cases W with
    | nil =>
      have : x.2 = v := h.1.2
      simp [liftW, this]
    | cons y W =>
      have ht := M.isPath_tail h
      have hxv : x.2 ≠ v := by
        intro he
        have hm := M.end_mem_snd ht.1 (List.cons_ne_nil _ _)
        rw [← he] at hm
        exact (List.nodup_cons.1 ht.2).1 hm
      have hx : x.2 ∉ Wset := hin x (by simp) hxv
      rw [← plus_of_not_mem Wset hx]
      exact isWalk_liftW ht (fun z hz => hin z (List.mem_cons_of_mem _ hz))
        (List.cons_ne_nil _ _)

omit hρ in
/-- The generic form of kinds (i) and (ii): the vertices after the start are pairwise
distinct, and a waypoint `w i` that is not split is not among them. -/
def Good (w : Fin (ℓ + 1) → V) (Wset : Finset V) (R : Fin ℓ → List (E × V)) : Prop :=
  M.IsSegs w R ∧ ((catW R).map Prod.snd).Nodup ∧
    ∀ i : Fin ℓ, w i.castSucc ∉ Wset → w i.castSucc ∉ (catW R).map Prod.snd

/-- The reduction of kinds (i) and (ii) to thm:main: if every split vertex is a waypoint
`w (j+1)`, consecutive waypoints differ and `w 0, …, w (ℓ-1)` are distinct, then a route of
length `L` exists iff the distance check passes and `G'` has pairwise vertex-disjoint shortest
paths from `w i⁺` to `w (i+1)⁻`. -/
theorem vroute_iff (hσ : ∀ x, M.step (σ x) (π x) (τ x)) (w : Fin (ℓ + 1) → V)
    (hW : ∀ v ∈ Wset, ∃ j : Fin ℓ, w j.succ = v) (hne : ∀ i : Fin ℓ, w i.castSucc ≠ w i.succ)
    (hcs : Function.Injective fun i : Fin ℓ => w i.castSucc) :
    (∃ R, M.Good w Wset R ∧ M.mlen (catW R) = M.wayLen w) ↔
      M.splitCheck σ τ π Wset w ∧
        (M.splitG σ τ π Wset).HasVertexSolution (fun i => plus Wset (w i.castSucc))
          (fun i => Sum.inl (w i.succ)) := by
  set S := M.splitG σ τ π Wset
  constructor
  · rintro ⟨R, ⟨hs, hnd, hfree⟩, hL⟩
    have heq := M.segs_eq hs hL
    rw [map_snd_catW, nodup_flatten_ofFn] at hnd
    obtain ⟨hnd1, hnd2⟩ := hnd
    have hRne : ∀ i, R i ≠ [] := fun i h0 => hne i (by have := hs i; rw [h0] at this; exact this)
    have hlast : ∀ j, w j.succ ∈ (R j).map Prod.snd := fun j => M.end_mem_snd (hs j) (hRne j)
    -- a waypoint `w i` is not among the vertices of `R i` after its start
    have hstart : ∀ i, w i.castSucc ∉ (R i).map Prod.snd := by
      intro i hi
      by_cases hw : w i.castSucc ∈ Wset
      · obtain ⟨j, hj⟩ := hW _ hw
        have hji : j ≠ i := fun e => hne i (by rw [← hj, e])
        exact hnd2 j i hji _ (hj ▸ hlast j) hi
      · exact hfree i hw (by rw [map_snd_catW, mem_flatten_ofFn]; exact ⟨i, hi⟩)
    have hpath : ∀ i, M.IsPath (w i.castSucc) (R i) (w i.succ) :=
      fun i => ⟨hs i, List.nodup_cons.2 ⟨hstart i, hnd1 i⟩⟩
    have hin : ∀ i, ∀ x ∈ R i, x.2 ≠ w i.succ → x.2 ∉ Wset := by
      intro i x hx hxv hxW
      obtain ⟨j, hj⟩ := hW _ hxW
      have hji : j ≠ i := fun e => hxv (by rw [← hj, e])
      exact hnd2 j i hji _ (hj ▸ hlast j) (List.mem_map_of_mem hx)
    let P : Fin ℓ → List (E' × (V ⊕ V)) := fun i => liftW ρ (w i.castSucc) (R i)
    have hPw : ∀ i, S.IsWalk (plus Wset (w i.castSucc)) (P i) (Sum.inl (w i.succ)) :=
      fun i => M.isWalk_liftW hρ (hpath i) (hin i) (hRne i)
    have hPv : ∀ i, verts (plus Wset (w i.castSucc)) (P i) =
        plus Wset (w i.castSucc) :: ((R i).map Prod.snd).map Sum.inl := fun i => by
      simp only [verts, P, map_snd_liftW]
    have hPl : ∀ i, S.mlen (P i) = M.dist (w i.castSucc) (w i.succ) := fun i => by
      rw [← heq i]; exact M.mlen_liftW hρ (hs i)
    have hPp : ∀ i, S.IsPath (plus Wset (w i.castSucc)) (P i) (Sum.inl (w i.succ)) := by
      intro i
      refine ⟨hPw i, ?_⟩
      rw [hPv i, List.nodup_cons]
      refine ⟨fun hm => ?_, (hnd1 i).map Sum.inl_injective⟩
      obtain ⟨a, ha, he⟩ := List.mem_map.1 hm
      obtain ⟨-, rfl⟩ := plus_eq_inl Wset he.symm
      exact hstart i ha
    refine ⟨fun i => ?_, P, fun i => ⟨hPp i, fun Q hQ => ?_⟩, ?_⟩
    · exact (S.dist_le_path (hPp i)).trans (hPl i).le
    · rw [hPl i, ← M.mlen_projW]
      have := M.isWalk_projW hσ hQ.1
      simp only [proj_plus, proj_inl] at this
      exact M.dist_le_walk this
    · intro i j hij v hv hv'
      rw [hPv i, List.mem_cons] at hv
      rw [hPv j, List.mem_cons] at hv'
      rcases hv with rfl | hv <;> rcases hv' with he | hv'
      · exact hij (hcs (by simpa using congrArg proj he))
      · obtain ⟨b, hb, he⟩ := List.mem_map.1 hv'
        obtain ⟨hnW, rfl⟩ := plus_eq_inl Wset he.symm
        exact hfree i hnW (by rw [map_snd_catW, mem_flatten_ofFn]; exact ⟨j, hb⟩)
      · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hv
        obtain ⟨hnW, rfl⟩ := plus_eq_inl Wset he.symm
        exact hfree j hnW (by rw [map_snd_catW, mem_flatten_ofFn]; exact ⟨i, ha⟩)
      · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hv
        obtain ⟨b, hb, he⟩ := List.mem_map.1 hv'
        rw [Sum.inl_injective he] at hb
        exact hnd2 i j hij a ha hb
  · rintro ⟨hchk, P, hP, hdis⟩
    let R : Fin ℓ → List (E × V) := fun i => projW π (P i)
    have hRw : ∀ i, M.IsWalk (w i.castSucc) (R i) (w i.succ) := fun i => by
      have := M.isWalk_projW hσ (hP i).1.1
      simpa using this
    have hRl : ∀ i, M.mlen (R i) = M.dist (w i.castSucc) (w i.succ) := fun i => by
      refine le_antisymm ?_ (M.dist_le_walk (hRw i))
      rw [M.mlen_projW, ← S.dist_eq (hP i)]
      exact hchk i
    -- the vertices of `P i` after its start are copies `inl v`
    have hinl : ∀ i, ∀ y ∈ (P i).map Prod.snd, y = Sum.inl (proj y) := by
      intro i y hy
      obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
      rw [M.snd_mem_splitG (hP i).1.1 hz]; rfl
    have hRv : ∀ i, (R i).map Prod.snd = ((P i).map Prod.snd).map proj := fun i =>
      map_snd_projW (π := π) (P i)
    have hmemR : ∀ i a, a ∈ (R i).map Prod.snd → Sum.inl a ∈ verts (plus Wset (w i.castSucc)) (P i) := by
      intro i a ha
      rw [hRv i] at ha
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 ha
      rw [← hinl i y hy]
      exact List.mem_cons_of_mem _ hy
    refine ⟨R, ⟨hRw, ?_, ?_⟩, ?_⟩
    · rw [map_snd_catW, nodup_flatten_ofFn]
      refine ⟨fun i => ?_, fun i j hij a ha ha' => hdis i j hij _ (hmemR i a ha) (hmemR j a ha')⟩
      rw [hRv i]
      refine List.Nodup.map_on (fun x hx y hy hxy => ?_) (List.nodup_cons.1 (hP i).1.2).2
      rw [hinl i x hx, hinl i y hy, hxy]
    · intro i hnW hm
      rw [map_snd_catW, mem_flatten_ofFn] at hm
      obtain ⟨j, hj⟩ := hm
      have h1 : Sum.inl (w i.castSucc) ∈ verts (plus Wset (w i.castSucc)) (P i) := by
        rw [plus_of_not_mem Wset hnW]; exact List.mem_cons_self
      by_cases hij : i = j
      · subst hij
        have hn : plus Wset (w i.castSucc) ∉ (P i).map Prod.snd :=
          (List.nodup_cons.1 (hP i).1.2).1
        rw [plus_of_not_mem Wset hnW] at hn
        rw [hRv i] at hj
        obtain ⟨y, hy, hyw⟩ := List.mem_map.1 hj
        exact hn (by rw [← hyw, ← hinl i y hy]; exact hy)
      · exact hdis i j hij _ h1 (hmemR j _ hj)
    · rw [mlen_catW, wayLen]
      exact Finset.sum_congr rfl fun i _ => hRl i

end Split

end MGraph

end DSPP
