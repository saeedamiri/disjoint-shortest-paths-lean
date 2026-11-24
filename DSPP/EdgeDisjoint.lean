/-
The arc- and edge-disjoint versions (prop:arcdisjoint, prop:edgedisjoint).

Paper: "Directed k Disjoint Shortest Paths Is Polynomial for Every Fixed k" (Saeed Amiri),
Section "Remarks and open problems".

Both reductions are instances of the line digraph with terminals of `LineGraph.lean`.
-/
import DSPP.LineGraph

open Classical

namespace DSPP

variable {V E : Type*} {k : ℕ}

/-- A multigraph is acyclic: its closed walks are the one-vertex walks. -/
def MGraph.Acyclic (M : MGraph V E) : Prop := ∀ a W, M.IsWalk a W a → W = []

/-- An instance is acyclic: no vertex reaches itself along one or more arcs. -/
def Instance.Acyclic {U : Type*} [Fintype U] [DecidableEq U] (G : Instance U k) : Prop :=
  ∀ v, ¬ Relation.TransGen G.arc v v

/-! ### prop:arcdisjoint -/

/-- prop:arcdisjoint, the digraph `L`: arcs `(x_a, x_b)` of length `ℓ(b)` for `a ≠ b` with
head of `a` = tail of `b`, arcs `(σ_i, x_a)` of length `ℓ(a)` for tail of `a` = `s_i`, and arcs
`(x_a, τ_i)` of length `1` for head of `a` = `t_i`. -/
def arcLine (src tgt : E → V) (len : E → ℝ) (hpos : ∀ e, 0 < len e) (s t : Fin k → V) :
    LineData E k where
  adj a b := a ≠ b ∧ tgt a = src b
  lxx _ b := len b
  st i a := src a = s i
  ls := len
  en i a := tgt a = t i
  le _ := 1
  lxx_pos _ b := hpos b
  ls_pos := hpos
  le_pos _ := one_pos

section Arc

variable (src tgt : E → V) (len : E → ℝ) (hpos : ∀ e, 0 < len e) (s t : Fin k → V)

theorem arcLine_tcost : ∀ (W : List E) (e : E),
    (arcLine src tgt len hpos s t).tcost e W = (W.map len).sum + 1 := by
  intro W
  induction W with
  | nil => intro e; simp [LineData.tcost, arcLine]
  | cons f W ih => intro e; simp only [LineData.tcost, ih, List.map_cons, List.sum_cons];
                   simp [arcLine]; ring

theorem arcLine_walk : ∀ (W : List E) (a b : V), W ≠ [] →
    W.IsChain (fun a b => tgt a = src b) → (∀ e ∈ W.head?, src e = a) →
    (∀ e ∈ W.getLast?, tgt e = b) →
    (MGraph.ofArcs src tgt len hpos).IsWalk a (W.map fun e => (e, tgt e)) b := by
  intro W
  induction W with
  | nil => intro a b h; exact absurd rfl h
  | cons e W ih =>
    intro a b _ hc hh hl
    refine ⟨⟨by simpa using hh, rfl⟩, ?_⟩
    cases W with
    | nil => simpa using hl
    | cons f W =>
      rw [List.isChain_cons_cons] at hc
      exact ih (tgt e) b (by simp) hc.2 (by simpa using hc.1.symm) (by simpa using hl)

variable [Fintype E] [DecidableEq E]

/-- prop:arcdisjoint.  Let `G` be a digraph with parallel arcs allowed (arcs `E`, arc `e` from
`src e` to `tgt e`), positive lengths, and pairs `(s_i, t_i)` with `s_i ≠ t_i`, where terminals
of different pairs may coincide.  Then `G` has pairwise arc-disjoint paths, each a shortest
`s_i`--`t_i` path, iff the line digraph `L` (`arcLine`) has pairwise vertex-disjoint paths, each a
shortest `σ_i`--`τ_i` path.  `L` is an `Instance`, so its lengths are positive and its `2k`
terminals are distinct; it has `|E| + 2k` vertices.  (`Instance` requires `k ≥ 2`.)  Every solution `Q` of `L` gives
such paths of `G`, `LineData.backSol G s t Q`. -/
theorem prop_arcdisjoint (hk : 2 ≤ k) (hst : ∀ i, s i ≠ t i) :
    (((MGraph.ofArcs src tgt len hpos).HasEdgeSolution s t ↔
      ((arcLine src tgt len hpos s t).inst hk).HasSolution) ∧
      ∀ Q, ((arcLine src tgt len hpos s t).inst hk).IsSolution Q →
        (MGraph.ofArcs src tgt len hpos).IsEdgeSolution s t
          (LineData.backSol (MGraph.ofArcs src tgt len hpos) s t Q)) ∧
    Fintype.card (E ⊕ (Fin k ⊕ Fin k)) = Fintype.card E + 2 * k := by
  refine ⟨?_, LineData.card_vertices⟩
  set M := MGraph.ofArcs src tgt len hpos
  set D := arcLine src tgt len hpos s t
  refine D.hasSolution_iff hk M s t 1 1 one_pos ?_ ?_ ?_
  · intro i P hP
    refine ⟨?_, M.nodup_edges hP, ?_, ?_, ?_⟩
    · have := M.ne_nil_of_isPath hP (hst i)
      simpa [MGraph.edges] using this
    · exact MGraph.isChain_ne_of_nodup (M.nodup_edges hP)
        (M.isChain_edges (fun a b => tgt a = src b) (fun h1 h2 => h1.2.trans h2.1.symm) hP.1)
    · intro e he
      obtain ⟨v, hv⟩ := M.head_step hP.1 e he
      exact hv.1
    · intro e he
      obtain ⟨u, hu⟩ := M.last_step hP.1 e he
      exact hu.2
  · intro i W hW
    obtain ⟨e, W', rfl⟩ := List.exists_cons_of_ne_nil hW.1
    rw [D.wlen_img hk, arcLine_tcost]
    simp [D, M, arcLine, MGraph.ofArcs]; ring
  · intro i W hW
    obtain ⟨hne, -, hc, hh, hl⟩ := hW
    have hw := arcLine_walk src tgt len hpos W (s i) (t i) hne (hc.imp fun _ _ h => h.2) hh hl
    obtain ⟨P, hP, hsub, hle⟩ := M.exists_path_of_walk hw
    refine ⟨P, hP, fun e he => ?_, ?_⟩
    · simpa [MGraph.edges, Function.comp_def] using hsub e he
    · refine hle.trans (le_of_eq ?_)
      rw [M.mlen_eq_sum]
      simp [M, MGraph.ofArcs, MGraph.edges, Function.comp_def]


omit [Fintype E] [DecidableEq E] in
/-- Along the arcs of `L`, a vertex `x_a` never reaches a source `σ_i`, and it reaches `x_b` only
if the digraph has a non-empty walk from the tail of `a` to the tail of `b`. -/
theorem arcLine_transGen {a : E} {y : E ⊕ (Fin k ⊕ Fin k)}
    (h : Relation.TransGen (arcLine src tgt len hpos s t).larc (.inl a) y) :
    (∀ i, y ≠ .inr (.inl i)) ∧ ∀ b, y = .inl b →
      ∃ W, W ≠ [] ∧ (MGraph.ofArcs src tgt len hpos).IsWalk (src a) W (src b) := by
  induction h with
  | @single y hab =>
    rcases y with b | j | j
    · have hab' : a ≠ b ∧ tgt a = src b := hab
      refine ⟨(fun _ h => by cases h), fun b' hb => ?_⟩
      obtain rfl := Sum.inl_injective hb
      exact ⟨[(a, tgt a)], by simp, ⟨rfl, rfl⟩, hab'.2⟩
    · exact (hab : False).elim
    · exact ⟨(fun _ h => by cases h), fun _ hb => by cases hb⟩
  | @tail c y _ hbc ih =>
    rcases c with c | i | i
    · rcases y with b | j | j
      · obtain ⟨W, -, hw⟩ := ih.2 c rfl
        have hbc' : c ≠ b ∧ tgt c = src b := hbc
        refine ⟨(fun _ h => by cases h), fun b' hb => ?_⟩
        obtain rfl := Sum.inl_injective hb
        exact ⟨W ++ [(c, tgt c)], by simp,
          (MGraph.ofArcs src tgt len hpos).isWalk_append hw ⟨⟨rfl, rfl⟩, hbc'.2⟩⟩
      · exact (hbc : False).elim
      · exact ⟨(fun _ h => by cases h), fun _ hb => by cases hb⟩
    · exact absurd rfl (ih.1 i)
    · rcases y with b | j | j <;> exact (hbc : False).elim

/-- prop:arcdisjoint, last part: `L` is acyclic if `G` is. -/
theorem prop_arcdisjoint_acyclic (hk : 2 ≤ k) (hG : (MGraph.ofArcs src tgt len hpos).Acyclic) :
    ((arcLine src tgt len hpos s t).inst hk).Acyclic := by
  intro v hv
  rcases v with a | i | i
  · obtain ⟨W, hW, hw⟩ := (arcLine_transGen src tgt len hpos s t hv).2 a rfl
    exact hW (hG _ _ hw)
  · obtain ⟨b, -, hb⟩ := Relation.TransGen.tail'_iff.1 hv
    rcases b with b | j | j <;> exact hb
  · obtain ⟨b, hb, -⟩ := Relation.TransGen.head'_iff.1 hv
    rcases b with b | j | j <;> exact hb

end Arc

/-! ### prop:edgedisjoint -/

/-- `x` is an end of the edge `e`. -/
def IsEnd (fst snd : E → V) (x : V) (e : E) : Prop := fst e = x ∨ snd e = x

/-- prop:edgedisjoint, the digraph `L`: arcs `(y_e, y_f)` of length `ℓ(e) + ℓ(f)` for `e ≠ f`
with a common end, arcs `(σ_i, y_e)` of length `ℓ(e)` for `s_i` an end of `e`, and arcs
`(y_e, τ_i)` of length `ℓ(e)` for `t_i` an end of `e`. -/
def edgeLine (fst snd : E → V) (len : E → ℝ) (hpos : ∀ e, 0 < len e) (s t : Fin k → V) :
    LineData E k where
  adj e f := e ≠ f ∧ ∃ x, IsEnd fst snd x e ∧ IsEnd fst snd x f
  lxx e f := len e + len f
  st i e := IsEnd fst snd (s i) e
  ls := len
  en i e := IsEnd fst snd (t i) e
  le := len
  lxx_pos e f := add_pos (hpos e) (hpos f)
  ls_pos := hpos
  le_pos := hpos

section Edge

variable (fst snd : E → V) (len : E → ℝ) (hpos : ∀ e, 0 < len e) (s t : Fin k → V)

theorem edgeLine_tcost : ∀ (W : List E) (e : E),
    (edgeLine fst snd len hpos s t).tcost e W = len e + 2 * (W.map len).sum := by
  intro W
  induction W with
  | nil => intro e; simp [LineData.tcost, edgeLine]
  | cons f W ih => intro e; simp only [LineData.tcost, ih, List.map_cons, List.sum_cons];
                   simp [edgeLine]; ring

theorem isEnd_left {u w : V} {e : E} (h : (MGraph.ofEdges fst snd len hpos).step u e w) :
    IsEnd fst snd u e := by
  rcases h with ⟨h, -⟩ | ⟨-, h⟩
  · exact Or.inl h
  · exact Or.inr h

theorem isEnd_right {u w : V} {e : E} (h : (MGraph.ofEdges fst snd len hpos).step u e w) :
    IsEnd fst snd w e := by
  rcases h with ⟨-, h⟩ | ⟨h, -⟩
  · exact Or.inr h
  · exact Or.inl h

/-- Two ends of one edge are joined by a walk that uses at most that edge. -/
theorem edge_walk_one {a b : V} {e : E} (ha : IsEnd fst snd a e) (hb : IsEnd fst snd b e) :
    ∃ R, (MGraph.ofEdges fst snd len hpos).IsWalk a R b ∧
      ∀ f ∈ MGraph.edges R, f = e := by
  by_cases hab : a = b
  · subst hab; exact ⟨[], rfl, by simp⟩
  · refine ⟨[(e, b)], ⟨?_, rfl⟩, by simp⟩
    show (fst e = a ∧ snd e = b) ∨ (fst e = b ∧ snd e = a)
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact absurd (ha.symm.trans hb) hab
    · exact Or.inl ⟨ha, hb⟩
    · exact Or.inr ⟨hb, ha⟩
    · exact absurd (ha.symm.trans hb) hab

/-- The edges of a `σ_i`--`τ_i` path of `L` form a connected subgraph containing `s_i` and
`t_i`: there is an `s_i`--`t_i` walk using only these edges. -/
theorem edge_walk : ∀ (W : List E) (a b : V), W ≠ [] →
    W.IsChain (fun e f => ∃ x, IsEnd fst snd x e ∧ IsEnd fst snd x f) →
    (∀ e ∈ W.head?, IsEnd fst snd a e) → (∀ e ∈ W.getLast?, IsEnd fst snd b e) →
    ∃ R, (MGraph.ofEdges fst snd len hpos).IsWalk a R b ∧ ∀ f ∈ MGraph.edges R, f ∈ W := by
  intro W
  induction W with
  | nil => intro a b h; exact absurd rfl h
  | cons e W ih =>
    intro a b _ hc hh hl
    have ha : IsEnd fst snd a e := hh e (by simp)
    cases W with
    | nil =>
      obtain ⟨R, hR, hRe⟩ := edge_walk_one fst snd len hpos ha (hl e (by simp))
      exact ⟨R, hR, fun f hf => by rw [hRe f hf]; simp⟩
    | cons f W =>
      rw [List.isChain_cons_cons] at hc
      obtain ⟨x, hxe, hxf⟩ := hc.1
      obtain ⟨R1, hR1, hR1e⟩ := edge_walk_one fst snd len hpos ha hxe
      obtain ⟨R2, hR2, hR2e⟩ := ih x b (by simp) hc.2 (by simpa using hxf) (by simpa using hl)
      refine ⟨R1 ++ R2, MGraph.isWalk_append _ hR1 hR2, fun g hg => ?_⟩
      simp only [MGraph.edges, List.map_append, List.mem_append] at hg
      rcases hg with hg | hg
      · rw [hR1e g hg]; simp
      · exact List.mem_cons_of_mem _ (hR2e g hg)

include hpos in
theorem sum_le_of_subset {l₁ l₂ : List E} (h1 : l₁.Nodup) (h : ∀ e ∈ l₁, e ∈ l₂) :
    (l₁.map len).sum ≤ (l₂.map len).sum := by
  obtain ⟨l, hp, hs⟩ := List.subperm_of_subset h1 h
  rw [← (hp.map len).sum_eq]
  exact (hs.map len).sum_le_sum
    (by simp only [List.mem_map]; rintro _ ⟨x, -, rfl⟩; exact (hpos x).le)

variable [Fintype E] [DecidableEq E]

/-- prop:edgedisjoint.  Let `G` be an undirected graph with parallel edges allowed (edges `E`,
edge `e` joining `fst e` and `snd e`), positive lengths, and pairs `(s_i, t_i)` with
`s_i ≠ t_i`, where terminals of different pairs may coincide.  Then `G` has pairwise
edge-disjoint paths, each a shortest `s_i`--`t_i` path, iff the digraph `L` (`edgeLine`) has
pairwise vertex-disjoint paths, each a shortest `σ_i`--`τ_i` path.  `L` is an `Instance`, so its
lengths are positive and its `2k` terminals are distinct; it has `|E| + 2k` vertices.
(`Instance` requires `k ≥ 2`.) -/
theorem prop_edgedisjoint (hk : 2 ≤ k) (hst : ∀ i, s i ≠ t i) :
    (((MGraph.ofEdges fst snd len hpos).HasEdgeSolution s t ↔
      ((edgeLine fst snd len hpos s t).inst hk).HasSolution) ∧
      ∀ Q, ((edgeLine fst snd len hpos s t).inst hk).IsSolution Q →
        (MGraph.ofEdges fst snd len hpos).IsEdgeSolution s t
          (LineData.backSol (MGraph.ofEdges fst snd len hpos) s t Q)) ∧
    Fintype.card (E ⊕ (Fin k ⊕ Fin k)) = Fintype.card E + 2 * k := by
  refine ⟨?_, LineData.card_vertices⟩
  set M := MGraph.ofEdges fst snd len hpos
  set D := edgeLine fst snd len hpos s t
  refine D.hasSolution_iff hk M s t 2 0 two_pos ?_ ?_ ?_
  · intro i P hP
    refine ⟨?_, M.nodup_edges hP, ?_, ?_, ?_⟩
    · have := M.ne_nil_of_isPath hP (hst i)
      simpa [MGraph.edges] using this
    · exact MGraph.isChain_ne_of_nodup (M.nodup_edges hP)
        (M.isChain_edges _ (fun h1 h2 => ⟨_, isEnd_right fst snd len hpos h1,
          isEnd_left fst snd len hpos h2⟩) hP.1)
    · intro e he
      obtain ⟨v, hv⟩ := M.head_step hP.1 e he
      exact isEnd_left fst snd len hpos hv
    · intro e he
      obtain ⟨u, hu⟩ := M.last_step hP.1 e he
      exact isEnd_right fst snd len hpos hu
  · intro i W hW
    obtain ⟨e, W', rfl⟩ := List.exists_cons_of_ne_nil hW.1
    rw [D.wlen_img hk, edgeLine_tcost]
    simp [D, M, edgeLine, MGraph.ofEdges]; ring
  · intro i W hW
    obtain ⟨hne, hnd, hc, hh, hl⟩ := hW
    obtain ⟨R, hR, hRW⟩ := edge_walk fst snd len hpos W (s i) (t i) hne (hc.imp fun _ _ h => h.2)
      hh hl
    obtain ⟨P, hP, hsub, -⟩ := M.exists_path_of_walk hR
    refine ⟨P, hP, fun e he => hRW e (hsub e he), ?_⟩
    rw [M.mlen_eq_sum]
    exact sum_le_of_subset len hpos (M.nodup_edges hP) (fun e he => hRW e (hsub e he))

end Edge

end DSPP
