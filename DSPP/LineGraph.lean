/-
Line digraphs with terminal vertices: the common part of prop:arcdisjoint and
prop:edgedisjoint.

Paper: "Directed k Disjoint Shortest Paths Is Polynomial for Every Fixed k" (Saeed Amiri),
Section "Remarks and open problems".

Both reductions build a digraph `L` with a vertex `x_e` for every arc or edge `e` and `2k`
further vertices `σ_i`, `τ_i`.  Its arcs are `(x_a, x_b)`, `(σ_i, x_a)` and `(x_a, τ_i)` under
conditions that depend on the reduction.  Here `L` is built from these conditions and lengths
(`LineData`); its vertex type is `E ⊕ (Fin k ⊕ Fin k)`, with `x_e = inl e`,
`σ_i = inr (inl i)` and `τ_i = inr (inr i)`.  Since no arc enters a `σ_j` or leaves a `τ_j`, a
`σ_i`--`τ_i` path of `L` is `σ_i, x_{e_1}, ..., x_{e_r}, τ_i` (`isPath_iff`).  `hasSolution_iff`
transfers solutions, given the two maps between paths that each proof provides.
-/
import DSPP.Multigraph

open Classical

namespace DSPP

/-- The arc conditions and lengths of a line digraph with terminals. -/
structure LineData (E : Type*) (k : ℕ) where
  /-- `(x_a, x_b)` is an arc. -/
  adj : E → E → Prop
  /-- The length of `(x_a, x_b)`. -/
  lxx : E → E → ℝ
  /-- `(σ_i, x_a)` is an arc. -/
  st : Fin k → E → Prop
  /-- The length of `(σ_i, x_a)`. -/
  ls : E → ℝ
  /-- `(x_a, τ_i)` is an arc. -/
  en : Fin k → E → Prop
  /-- The length of `(x_a, τ_i)`. -/
  le : E → ℝ
  lxx_pos : ∀ a b, 0 < lxx a b
  ls_pos : ∀ a, 0 < ls a
  le_pos : ∀ a, 0 < le a

namespace LineData

variable {E : Type*} {k : ℕ} (D : LineData E k)

/-- The arc relation of `L`. -/
def larc : E ⊕ (Fin k ⊕ Fin k) → E ⊕ (Fin k ⊕ Fin k) → Prop
  | .inl a, .inl b => D.adj a b
  | .inr (.inl i), .inl a => D.st i a
  | .inl a, .inr (.inr i) => D.en i a
  | _, _ => False

/-- The length function of `L` (its values off the arcs are not used). -/
def llen : E ⊕ (Fin k ⊕ Fin k) → E ⊕ (Fin k ⊕ Fin k) → ℝ
  | .inl a, .inl b => D.lxx a b
  | .inr (.inl _), .inl a => D.ls a
  | .inl a, .inr (.inr _) => D.le a
  | _, _ => 1

theorem llen_pos (u v : E ⊕ (Fin k ⊕ Fin k)) : 0 < D.llen u v := by
  rcases u with a | i | i <;> rcases v with b | j | j <;>
    simp [llen, D.lxx_pos, D.ls_pos, D.le_pos]

variable [Fintype E] [DecidableEq E]

/-- The digraph `L` as an instance: terminals `σ_i = inr (inl i)` and `τ_i = inr (inr i)`. -/
def inst (hk : 2 ≤ k) : Instance (E ⊕ (Fin k ⊕ Fin k)) k where
  arc := D.larc
  len := D.llen
  len_pos u v _ := D.llen_pos u v
  s i := .inr (.inl i)
  t i := .inr (.inr i)
  terminals_injective := by
    intro x y h
    rcases x with i | i <;> rcases y with j | j <;> simp_all
  two_le_k := hk

/-- `L` has `|E| + 2k` vertices. -/
theorem card_vertices : Fintype.card (E ⊕ (Fin k ⊕ Fin k)) = Fintype.card E + 2 * k := by
  simp [Fintype.card_sum]; ring

/-- The `σ_i`--`τ_i` path `σ_i, x_{e_1}, ..., x_{e_r}, τ_i` of the list `W = e_1, ..., e_r`. -/
def img (i : Fin k) (W : List E) : List (E ⊕ (Fin k ⊕ Fin k)) :=
  .inr (.inl i) :: (W.map .inl ++ [.inr (.inr i)])

theorem mem_img {i : Fin k} {W : List E} {v : E ⊕ (Fin k ⊕ Fin k)} :
    v ∈ img i W ↔ v = .inr (.inl i) ∨ (∃ e ∈ W, v = .inl e) ∨ v = .inr (.inr i) := by
  simp only [img, List.mem_cons, List.mem_append, List.mem_map, List.mem_nil_iff, or_false]
  constructor
  · rintro (h | ⟨e, he, rfl⟩ | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨e, he, rfl⟩)
    · exact Or.inr (Or.inr h)
  · rintro (h | ⟨e, he, rfl⟩ | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨e, he, rfl⟩)
    · exact Or.inr (Or.inr h)

theorem getLast?_img (i : Fin k) (W : List E) : (img i W).getLast? = some (.inr (.inr i)) := by
  show (((Sum.inr (Sum.inl i) : E ⊕ (Fin k ⊕ Fin k)) :: W.map Sum.inl) ++
    [Sum.inr (Sum.inr i)]).getLast? = _
  exact List.getLast?_concat

theorem nodup_img {i : Fin k} {W : List E} (h : W.Nodup) : (img i W).Nodup := by
  rw [img, List.nodup_cons, List.nodup_append]
  refine ⟨?_, h.map Sum.inl_injective, List.nodup_singleton _, ?_⟩
  · simp
  · simp

/-- The lists `W` whose `img` is a `σ_i`--`τ_i` path. -/
def IsLW (i : Fin k) (W : List E) : Prop :=
  W ≠ [] ∧ W.Nodup ∧ W.IsChain D.adj ∧ (∀ e ∈ W.head?, D.st i e) ∧ (∀ e ∈ W.getLast?, D.en i e)

theorem tail_form (i : Fin k) :
    ∀ (rest : List (E ⊕ (Fin k ⊕ Fin k))) (e : E), (.inl e :: rest).IsChain D.larc →
      (.inl e :: rest).getLast? = some (.inr (.inr i)) →
      ∃ W, rest = W.map .inl ++ [.inr (.inr i)] ∧ (e :: W).IsChain D.adj ∧
        ∀ f ∈ (e :: W).getLast?, D.en i f := by
  intro rest
  induction rest with
  | nil => intro e _ h; simp at h
  | cons x rest ih =>
    intro e hc hl
    rw [List.isChain_cons_cons] at hc
    rcases x with f | j | j
    · obtain ⟨W, rfl, hW, hen⟩ := ih f hc.2 (by simpa using hl)
      refine ⟨f :: W, rfl, List.isChain_cons_cons.2 ⟨hc.1, hW⟩, ?_⟩
      simpa using hen
    · exact absurd hc.1 (by simp [larc])
    · cases rest with
      | nil =>
        simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq,
          Sum.inr.injEq] at hl
        subst hl
        exact ⟨[], by simp, by simp, by simpa [larc] using hc.1⟩
      | cons y rest =>
        rw [List.isChain_cons_cons] at hc
        exact absurd hc.2.1 (by rcases y with _ | _ | _ <;> simp [larc])

theorem isChain_img_tail (i : Fin k) :
    ∀ (W : List E) (e : E), (e :: W).IsChain D.adj → (∀ f ∈ (e :: W).getLast?, D.en i f) →
      (.inl e :: (W.map .inl ++ [.inr (.inr i)])).IsChain D.larc := by
  intro W
  induction W with
  | nil => intro e _ h; simpa [larc] using h
  | cons f W ih =>
    intro e hc hl
    rw [List.isChain_cons_cons] at hc
    simp only [List.map_cons, List.cons_append]
    rw [List.isChain_cons_cons]
    exact ⟨hc.1, ih f hc.2 (by simpa using hl)⟩

/-- The `σ_i`--`τ_i` paths of `L` are the lists `img i W` with `IsLW i W`. -/
theorem isPath_iff (hk : 2 ≤ k) (i : Fin k) (Q : List (E ⊕ (Fin k ⊕ Fin k))) :
    (D.inst hk).IsPath Q (.inr (.inl i)) (.inr (.inr i)) ↔ ∃ W, Q = img i W ∧ D.IsLW i W := by
  constructor
  · rintro ⟨⟨hh, hl, hc⟩, hnd⟩
    obtain ⟨Q', rfl⟩ := List.head?_eq_some_iff.1 hh
    cases Q' with
    | nil => simp at hl
    | cons y Q' =>
      rw [List.isChain_cons_cons] at hc
      rcases y with e | j | j
      · obtain ⟨W, rfl, hW, hen⟩ := D.tail_form i Q' e hc.2 (by simpa using hl)
        refine ⟨e :: W, rfl, by simp, ?_, hW, by simpa [inst, larc] using hc.1, hen⟩
        have h2 := (List.nodup_cons.1 hnd).2
        rw [← List.cons_append] at h2
        exact (List.Nodup.of_append_left h2 : ((e :: W).map Sum.inl).Nodup).of_map _
      · exact absurd hc.1 (by simp [inst, larc])
      · exact absurd hc.1 (by simp [inst, larc])
  · rintro ⟨W, rfl, hne, hnd, hc, hst, hen⟩
    obtain ⟨e, W', rfl⟩ := List.exists_cons_of_ne_nil hne
    refine ⟨⟨by simp [img], getLast?_img i _, ?_⟩, nodup_img hnd⟩
    · simp only [img, List.map_cons, List.cons_append]
      rw [List.isChain_cons_cons]
      exact ⟨by simpa [inst, larc] using hst, D.isChain_img_tail i W' e hc hen⟩

/-- The cost of `x_e, x_{w_1}, ..., x_{w_r}, τ`. -/
def tcost : E → List E → ℝ
  | e, [] => D.le e
  | e, f :: W => D.lxx e f + tcost f W

theorem wlen_tail (hk : 2 ≤ k) (i : Fin k) :
    ∀ (W : List E) (e : E),
      (D.inst hk).wlen (.inl e :: (W.map .inl ++ [.inr (.inr i)])) = D.tcost e W := by
  intro W
  induction W with
  | nil => intro e; simp [Instance.wlen_cons_cons, Instance.wlen_singleton, tcost, inst, llen]
  | cons f W ih =>
    intro e
    simp only [List.map_cons, List.cons_append]
    rw [Instance.wlen_cons_cons, ih f]
    simp [tcost, inst, llen]

theorem wlen_img (hk : 2 ≤ k) (i : Fin k) (e : E) (W : List E) :
    (D.inst hk).wlen (img i (e :: W)) = D.ls e + D.tcost e W := by
  simp only [img, List.map_cons, List.cons_append]
  rw [Instance.wlen_cons_cons, D.wlen_tail hk i W e]
  simp [inst, llen]

/-- The arcs or edges `W` of a path `img i W` of `L`. -/
def lw (Q : List (E ⊕ (Fin k ⊕ Fin k))) : List E := Q.filterMap Sum.getLeft?

omit [Fintype E] [DecidableEq E] in
theorem lw_img (i : Fin k) (W : List E) : lw (img i W) = W := by
  unfold lw img
  rw [List.filterMap_cons, List.filterMap_append, List.filterMap_map]
  simp [Function.comp_def]

omit [Fintype E] [DecidableEq E] in
/-- A path of `M` from `a` to `b` that uses only arcs or edges of `W` and is not longer than `W`,
if there is one (a pick among the finitely many paths inside `W`). -/
noncomputable def pathIn {V : Type*} (M : MGraph V E) (a b : V) (W : List E) : List (E × V) :=
  if h : ∃ P, M.IsPath a P b ∧ (∀ e ∈ MGraph.edges P, e ∈ W) ∧ M.mlen P ≤ (W.map M.len).sum
  then h.choose else []

omit [Fintype E] [DecidableEq E] in
theorem pathIn_spec {V : Type*} {M : MGraph V E} {a b : V} {W : List E}
    (h : ∃ P, M.IsPath a P b ∧ (∀ e ∈ MGraph.edges P, e ∈ W) ∧ M.mlen P ≤ (W.map M.len).sum) :
    M.IsPath a (pathIn M a b W) b ∧ (∀ e ∈ MGraph.edges (pathIn M a b W), e ∈ W) ∧
      M.mlen (pathIn M a b W) ≤ (W.map M.len).sum := by
  unfold pathIn
  rw [dif_pos h]
  exact h.choose_spec

omit [Fintype E] [DecidableEq E] in
/-- The paths of `M` read off paths `Q` of `L`: for each `i`, a path of `M` inside the arcs or
edges that `Q i` visits. -/
noncomputable def backSol {V : Type*} (M : MGraph V E) (s t : Fin k → V)
    (Q : Fin k → List (E ⊕ (Fin k ⊕ Fin k))) : Fin k → List (E × V) :=
  fun i => pathIn M (s i) (t i) (lw (Q i))

/-- Under the hypotheses of `hasSolution_iff`, `backSol` maps every solution of `L` to `k`
pairwise arc- or edge-disjoint shortest paths of `M`. -/
theorem isEdgeSolution_backSol {V : Type*} (hk : 2 ≤ k) (M : MGraph V E) (s t : Fin k → V)
    (α β : ℝ) (hα : 0 < α)
    (hfwd : ∀ i P, M.IsPath (s i) P (t i) → D.IsLW i (MGraph.edges P))
    (hcost : ∀ i W, D.IsLW i W → (D.inst hk).wlen (img i W) = α * (W.map M.len).sum + β)
    (hback : ∀ i W, D.IsLW i W → ∃ P, M.IsPath (s i) P (t i) ∧
      (∀ e ∈ MGraph.edges P, e ∈ W) ∧ M.mlen P ≤ (W.map M.len).sum)
    (Q : Fin k → List (E ⊕ (Fin k ⊕ Fin k))) (hQs : (D.inst hk).IsSolution Q) :
    M.IsEdgeSolution s t (backSol M s t Q) := by
  have hml : ∀ P : List (E × V), M.mlen P = ((MGraph.edges P).map M.len).sum := by
    intro P; simp [MGraph.mlen, MGraph.edges, Function.comp_def]
  obtain ⟨hQ, hdis⟩ := hQs
  have hQW : ∀ i, Q i = img i (lw (Q i)) ∧ D.IsLW i (lw (Q i)) := fun i => by
    obtain ⟨W', hQ', hW'⟩ := (D.isPath_iff hk i (Q i)).1 (hQ i).1
    rw [hQ', lw_img]
    exact ⟨rfl, hW'⟩
  have hspec := fun i => pathIn_spec (hback i (lw (Q i)) (hQW i).2)
  refine ⟨fun i => ⟨(hspec i).1, fun P' hP' => ?_⟩, ?_⟩
  · have h1 := (hQ i).2 _ ((D.isPath_iff hk i _).2 ⟨_, rfl, hfwd i _ hP'⟩)
    rw [(hQW i).1, hcost i _ (hQW i).2, hcost i _ (hfwd i _ hP'), ← hml] at h1
    have : ((lw (Q i)).map M.len).sum ≤ M.mlen P' := by nlinarith
    exact (hspec i).2.2.trans this
  · intro i j hij e he he'
    refine hdis i j hij (.inl e) ?_ ?_
    · rw [(hQW i).1, mem_img]; exact Or.inr (Or.inl ⟨e, (hspec i).2.1 e he, rfl⟩)
    · rw [(hQW j).1, mem_img]; exact Or.inr (Or.inl ⟨e, (hspec j).2.1 e he', rfl⟩)

/-- Transfer of solutions.  Let `M` be a multigraph with terminals `s`, `t` and arcs or edges
`E`.  Assume that
* the arcs or edges of every `s_i`--`t_i` path of `M` form a list `W` with `IsLW i W`;
* for `IsLW i W` the path `img i W` has length `α ℓ(W) + β` with `α > 0`, where `ℓ(W)` is the
  sum of the lengths of `W`;
* for `IsLW i W` there is an `s_i`--`t_i` path of `M` whose arcs or edges lie in `W` and whose
  length is at most `ℓ(W)`.
Then `M` has `k` pairwise arc- or edge-disjoint shortest paths if and only if `L` has `k`
pairwise vertex-disjoint shortest paths. -/
theorem hasSolution_iff {V : Type*} (hk : 2 ≤ k) (M : MGraph V E) (s t : Fin k → V)
    (α β : ℝ) (hα : 0 < α)
    (hfwd : ∀ i P, M.IsPath (s i) P (t i) → D.IsLW i (MGraph.edges P))
    (hcost : ∀ i W, D.IsLW i W → (D.inst hk).wlen (img i W) = α * (W.map M.len).sum + β)
    (hback : ∀ i W, D.IsLW i W → ∃ P, M.IsPath (s i) P (t i) ∧
      (∀ e ∈ MGraph.edges P, e ∈ W) ∧ M.mlen P ≤ (W.map M.len).sum) :
    (M.HasEdgeSolution s t ↔ (D.inst hk).HasSolution) ∧
      ∀ Q, (D.inst hk).IsSolution Q → M.IsEdgeSolution s t (backSol M s t Q) := by
  have hml : ∀ P : List (E × V), M.mlen P = ((MGraph.edges P).map M.len).sum := by
    intro P; simp [MGraph.mlen, MGraph.edges, Function.comp_def]
  refine ⟨⟨?_, fun h => ?_⟩,
    fun Q hQ => D.isEdgeSolution_backSol hk M s t α β hα hfwd hcost hback Q hQ⟩
  · rintro ⟨P, hP, hdis⟩
    refine ⟨fun i => img i (MGraph.edges (P i)), fun i => ⟨?_, ?_⟩, ?_⟩
    · exact (D.isPath_iff hk i _).2 ⟨_, rfl, hfwd i _ (hP i).1⟩
    · intro R hR
      obtain ⟨W, rfl, hW⟩ := (D.isPath_iff hk i R).1 hR
      obtain ⟨P', hP', -, hle⟩ := hback i W hW
      rw [hcost i _ (hfwd i _ (hP i).1), hcost i W hW, ← hml]
      have := (hP i).2 P' hP'
      nlinarith
    · intro i j hij v hv hv'
      rw [mem_img] at hv hv'
      rcases hv with rfl | ⟨e, he, rfl⟩ | rfl <;> rcases hv' with h | ⟨e', he', h⟩ | h <;>
        simp only [Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at h
      · exact hij h
      · subst h; exact hdis i j hij e he he'
      · exact hij h
  · obtain ⟨Q, hQ⟩ := h
    exact ⟨_, D.isEdgeSolution_backSol hk M s t α β hα hfwd hcost hback Q hQ⟩

end LineData

end DSPP
