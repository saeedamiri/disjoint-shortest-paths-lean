/-
Trimming parallel arcs or edges (proof of cor:edgedisjoint).

Paper: "Directed k Disjoint Shortest Paths Is Polynomial for Every Fixed k" (Saeed Amiri),
Section "Remarks and open problems", proof of cor:edgedisjoint.

Every arc or edge `e` has a pair `pr e` (its ordered pair of ends for arcs, its unordered pair of
ends for edges).  For every pair that is not a loop we keep at most `k` arcs or edges of minimum
length with that pair and delete all others.  With `k` pairs of terminals this changes neither
the distances nor the answer of the arc- or edge-disjoint problem (`hasEdgeSolution_trim_iff`),
and at most `k` arcs or edges per pair remain (`card_kept_le`).
-/
import DSPP.Multigraph

open Classical

namespace DSPP

namespace MGraph

variable {V E P : Type*} [Fintype E] (M : MGraph V E) (pr : E → P) (loopP : P → Prop)

/-- The arcs or edges of minimum length among those with pair `p`. -/
noncomputable def minSet (p : P) : Finset E :=
  Finset.univ.filter fun e => pr e = p ∧ ∀ f, pr f = p → M.len e ≤ M.len f

/-- The arcs or edges of minimum length with pair `p`, listed in a fixed order. -/
noncomputable def minList (p : P) : List E := (M.minSet pr p).toList

/-- The kept arcs or edges: not a loop, and among the first `k` of `minList` of its pair. -/
def Kept (k : ℕ) (e : E) : Prop := ¬ loopP (pr e) ∧ e ∈ (M.minList pr (pr e)).take k

theorem mem_minList {p : P} {e : E} :
    e ∈ M.minList pr p ↔ pr e = p ∧ ∀ f, pr f = p → M.len e ≤ M.len f := by
  simp [minList, minSet]

theorem nodup_minList (p : P) : (M.minList pr p).Nodup := Finset.nodup_toList _

/-- The minimum is attained: `minList` of the pair of `e` is not empty. -/
theorem minList_ne_nil (e : E) : M.minList pr (pr e) ≠ [] := by
  obtain ⟨f, hf, hmin⟩ := Finset.exists_min_image (Finset.univ.filter fun f => pr f = pr e)
    M.len ⟨e, by simp⟩
  intro h
  have : f ∈ M.minList pr (pr e) := by
    rw [mem_minList]
    refine ⟨(Finset.mem_filter.1 hf).2, fun g hg => hmin g (by simp [hg])⟩
  rw [h] at this
  simp at this

variable {k : ℕ}

/-- The replacement of `e` in the `i`-th path: `e` itself if all arcs or edges of minimum
length with its pair are kept, otherwise the `i`-th of them. -/
noncomputable def repl (i : Fin k) (e : E) : E :=
  if h : k < (M.minList pr (pr e)).length then (M.minList pr (pr e))[i.1]'(i.2.trans h) else e

/-- The replacement used for comparisons: the first arc or edge of minimum length with the same
pair. -/
noncomputable def repl0 (e : E) : E := (M.minList pr (pr e)).head (M.minList_ne_nil pr e)

variable {pr loopP}

variable (hsub : ∀ {u w : V} {e f : E}, M.step u e w → pr f = pr e → M.step u f w)
variable (hloop : ∀ {u w : V} {e : E}, M.step u e w → loopP (pr e) → u = w)

include hsub in
/-- An arc or edge of a shortest path has minimum length among those with its pair. -/
theorem mem_minList_of_shortest {a b : V} {W : List (E × V)} (h : M.IsShortestPath a W b)
    {x : E × V} (hx : x ∈ W) : x.1 ∈ M.minList pr (pr x.1) := by
  rw [mem_minList]
  refine ⟨rfl, fun f hf => ?_⟩
  by_contra hlt
  push_neg at hlt
  let φ : E → E := fun e => if e = x.1 then f else e
  have hφ : ∀ y ∈ W, ∀ u, M.step u y.1 y.2 → M.step u (φ y.1) y.2 := by
    intro y _ u hs
    by_cases hy : y.1 = x.1
    · simp only [φ, hy, if_true]; exact hsub (hy ▸ hs) hf
    · simp only [φ, hy, if_false]; exact hs
  have hP := M.isPath_map M φ hφ h.1
  have h2 := h.2 _ hP
  obtain ⟨A, B, rfl⟩ := List.append_of_mem hx
  have hA := M.mlen_map_le M φ (W := A) (fun y _ => by
    by_cases hy : y.1 = x.1
    · simp only [φ, hy, if_true]; exact hlt.le
    · simp [φ, hy])
  have hB := M.mlen_map_le M φ (W := B) (fun y _ => by
    by_cases hy : y.1 = x.1
    · simp only [φ, hy, if_true]; exact hlt.le
    · simp [φ, hy])
  simp only [List.map_append, List.map_cons, mlen_append, mlen_cons, Prod.map_fst] at h2
  simp only [φ, if_true] at h2
  linarith

theorem repl_mem (i : Fin k) {e : E} (he : e ∈ M.minList pr (pr e)) :
    M.repl pr i e ∈ M.minList pr (pr e) := by
  unfold repl
  split_ifs with h
  · exact List.getElem_mem _
  · exact he

theorem pr_repl (i : Fin k) {e : E} (he : e ∈ M.minList pr (pr e)) :
    pr (M.repl pr i e) = pr e := ((M.mem_minList pr).1 (M.repl_mem i he)).1

theorem len_repl (i : Fin k) {e : E} (he : e ∈ M.minList pr (pr e)) :
    M.len (M.repl pr i e) = M.len e := by
  have h1 := (M.mem_minList pr).1 (M.repl_mem i he)
  have h2 := (M.mem_minList pr).1 he
  exact le_antisymm (h1.2 e rfl) (h2.2 _ h1.1)

theorem kept_repl (i : Fin k) {e : E} (he : e ∈ M.minList pr (pr e)) (hl : ¬ loopP (pr e)) :
    M.Kept pr loopP k (M.repl pr i e) := by
  refine ⟨by rw [M.pr_repl i he]; exact hl, ?_⟩
  rw [M.pr_repl i he]
  unfold repl
  split_ifs with h
  · rw [List.mem_iff_getElem]
    exact ⟨i.1, by rw [List.length_take]; have := i.2; omega, by simp⟩
  · rw [List.take_of_length_le (not_lt.1 h)]; exact he

theorem repl_inj {i j : Fin k} {e f : E} (he : e ∈ M.minList pr (pr e))
    (hf : f ∈ M.minList pr (pr f)) (h : M.repl pr i e = M.repl pr j f) : e = f ∨ i = j := by
  have hp : pr e = pr f := by rw [← M.pr_repl i he, ← M.pr_repl j hf, h]
  have key : ∀ (L L' : List E), L = L' → L.Nodup → ∀ (h1 : i.1 < L.length)
      (h2 : j.1 < L'.length), L[i.1] = L'[j.1] → i = j := by
    rintro L _ rfl hn h1 h2 hij
    exact Fin.ext ((List.Nodup.getElem_inj_iff hn).1 hij)
  unfold repl at h
  by_cases h1 : k < (M.minList pr (pr e)).length
  · have h2 : k < (M.minList pr (pr f)).length := by rw [← hp]; exact h1
    rw [dif_pos h1, dif_pos h2] at h
    exact Or.inr (key _ _ (by rw [hp]) (M.nodup_minList pr (pr e)) _ _ h)
  · have h2 : ¬ k < (M.minList pr (pr f)).length := by rw [← hp]; exact h1
    rw [dif_neg h1, dif_neg h2] at h
    exact Or.inl h

theorem repl0_mem (e : E) : M.repl0 pr e ∈ M.minList pr (pr e) := List.head_mem _

theorem pr_repl0 (e : E) : pr (M.repl0 pr e) = pr e :=
  ((M.mem_minList pr).1 (M.repl0_mem e)).1

theorem len_repl0 (e : E) : M.len (M.repl0 pr e) ≤ M.len e :=
  ((M.mem_minList pr).1 (M.repl0_mem e)).2 e rfl

theorem kept_repl0 (hk : 1 ≤ k) (e : E) (hl : ¬ loopP (pr e)) :
    M.Kept pr loopP k (M.repl0 pr e) := by
  refine ⟨by rw [M.pr_repl0 (pr := pr)]; exact hl, ?_⟩
  rw [M.pr_repl0 (pr := pr)]
  unfold repl0
  obtain ⟨g, l, hl'⟩ := List.exists_cons_of_ne_nil (M.minList_ne_nil pr e)
  simp only [hl', List.head_cons]
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  simp

variable (s t : Fin k → V)

include hsub hloop in
/-- Trimming preserves the answer: with `k` pairs of terminals, keeping at most `k` arcs or
edges of minimum length per pair (and no loops) changes neither the distances nor the existence
of `k` pairwise arc- or edge-disjoint shortest paths. -/
theorem hasEdgeSolution_trim_iff (hk : 1 ≤ k) :
    M.HasEdgeSolution s t ↔ (M.restrict (M.Kept pr loopP k)).HasEdgeSolution s t := by
  -- Every path of `M` gives a path of the trimmed multigraph that is not longer.
  have hshort : ∀ a b (R : List (E × V)), M.IsPath a R b → ∃ R',
      (M.restrict (M.Kept pr loopP k)).IsPath a R' b ∧
        (M.restrict (M.Kept pr loopP k)).mlen R' ≤ M.mlen R := by
    intro a b R hR
    have hφ : ∀ y ∈ R, ∀ u, M.step u y.1 y.2 → M.step u (M.repl0 pr y.1) y.2 :=
      fun y _ u hs => hsub hs (M.pr_repl0 y.1)
    have hP := M.isPath_map M _ hφ hR
    obtain ⟨R', hR', hmap⟩ := M.exists_restrict hP.1 (p := M.Kept pr loopP k) (by
      intro e he
      rw [edges_map] at he
      obtain ⟨g, hg, rfl⟩ := List.mem_map.1 he
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hg
      obtain ⟨u, hs, hne⟩ := M.step_ne_of_isPath hR hy
      exact M.kept_repl0 hk _ (fun hl => hne (hloop hs hl)))
    refine ⟨R', ⟨hR', ?_⟩, ?_⟩
    · have := hP.2
      rw [← hmap, verts_map] at this
      exact this
    · rw [← M.mlen_restrict, hmap]
      exact M.mlen_map_le M _ (fun y _ => M.len_repl0 y.1)
  constructor
  · rintro ⟨P, hP, hdis⟩
    have hmin : ∀ i, ∀ x ∈ P i, x.1 ∈ M.minList pr (pr x.1) :=
      fun i x hx => M.mem_minList_of_shortest hsub (hP i) hx
    have hnl : ∀ i, ∀ x ∈ P i, ¬ loopP (pr x.1) := by
      intro i x hx hl
      obtain ⟨u, hs, hne⟩ := M.step_ne_of_isPath (hP i).1 hx
      exact hne (hloop hs hl)
    have hφ : ∀ i, ∀ y ∈ P i, ∀ u, M.step u y.1 y.2 → M.step u (M.repl pr i y.1) y.2 :=
      fun i y hy u hs => hsub hs (M.pr_repl i (hmin i y hy))
    have hQ : ∀ i, ∃ Q, (M.restrict (M.Kept pr loopP k)).IsWalk (s i) Q (t i) ∧
        Q.map (Prod.map Subtype.val id) = (P i).map (Prod.map (M.repl pr i) id) := by
      intro i
      refine M.exists_restrict (M.isPath_map M _ (hφ i) (hP i).1).1 ?_
      intro e he
      rw [edges_map] at he
      obtain ⟨g, hg, rfl⟩ := List.mem_map.1 he
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hg
      exact M.kept_repl i (hmin i y hy) (hnl i y hy)
    choose Q hQ hQP using hQ
    have hQpath : ∀ i, (M.restrict (M.Kept pr loopP k)).IsPath (s i) (Q i) (t i) := by
      intro i
      refine ⟨hQ i, ?_⟩
      have := (hP i).1.2
      rw [← verts_map (M.repl pr i), ← hQP i, verts_map] at this
      exact this
    have hQlen : ∀ i, (M.restrict (M.Kept pr loopP k)).mlen (Q i) = M.mlen (P i) := by
      intro i
      rw [← M.mlen_restrict, hQP i]
      exact M.mlen_map_eq M _ (fun y hy => M.len_repl i (hmin i y hy))
    refine ⟨Q, fun i => ⟨hQpath i, fun R hR => ?_⟩, ?_⟩
    · rw [hQlen i, ← M.mlen_restrict]
      exact (hP i).2 _ (M.isPath_restrict hR)
    · intro i j hij e he he'
      have h1 : e.1 ∈ (edges (P i)).map (M.repl pr i) := by
        rw [← edges_map, ← hQP i, edges_map]; exact List.mem_map_of_mem he
      have h2 : e.1 ∈ (edges (P j)).map (M.repl pr j) := by
        rw [← edges_map, ← hQP j, edges_map]; exact List.mem_map_of_mem he'
      obtain ⟨f, hf, hfe⟩ := List.mem_map.1 h1
      obtain ⟨g, hg, hge⟩ := List.mem_map.1 h2
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hf
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hg
      rcases M.repl_inj (hmin i x hx) (hmin j y hy) (hfe.trans hge.symm) with h | h
      · exact hdis i j hij x.1 (List.mem_map_of_mem hx) (h ▸ List.mem_map_of_mem hy)
      · exact hij h
  · rintro ⟨Q, hQ, hdis⟩
    refine ⟨fun i => (Q i).map (Prod.map Subtype.val id), fun i => ⟨M.isPath_restrict (hQ i).1,
      fun R hR => ?_⟩, ?_⟩
    · obtain ⟨R', hR', hle⟩ := hshort _ _ R hR
      rw [M.mlen_restrict]
      exact ((hQ i).2 R' hR').trans hle
    · intro i j hij e he he'
      rw [edges_map] at he he'
      obtain ⟨f, hf, rfl⟩ := List.mem_map.1 he
      obtain ⟨g, hg, hgf⟩ := List.mem_map.1 he'
      exact hdis i j hij f hf (Subtype.ext hgf ▸ hg)

/-- At most `k` arcs or edges are kept per pair that is not a loop. -/
theorem card_kept_le [Fintype P] (k : ℕ) :
    (Finset.univ.filter (M.Kept pr loopP k)).card ≤
      k * (Finset.univ.filter fun p => ¬ loopP p).card := by
  refine (Finset.card_le_mul_card_image (f := pr) _ k ?_).trans (Nat.mul_le_mul_left _ ?_)
  · intro p _
    calc (Finset.univ.filter (M.Kept pr loopP k) |>.filter fun e => pr e = p).card
        ≤ ((M.minList pr p).take k).toFinset.card := by
          apply Finset.card_le_card
          intro e he
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
          obtain ⟨⟨-, h⟩, rfl⟩ := he
          exact List.mem_toFinset.2 h
      _ ≤ ((M.minList pr p).take k).length := List.toFinset_card_le _
      _ ≤ k := List.length_take_le _ _
  · apply Finset.card_le_card
    intro p hp
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hp
    simpa using (Finset.mem_filter.1 he).2.1

end MGraph

end DSPP
