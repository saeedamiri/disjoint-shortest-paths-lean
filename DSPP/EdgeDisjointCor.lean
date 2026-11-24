/-
The arc- and edge-disjoint versions are solvable in polynomial time for fixed `k`
(cor:edgedisjoint).

Paper: "Directed k Disjoint Shortest Paths Is Polynomial for Every Fixed k" (Saeed Amiri),
Section "Introduction" (statement) and Section "Remarks and open problems" (proof).

The reduced instance is built in two steps, as in the paper: trim the parallel arcs or edges to
at most `k` of minimum length per pair of ends, with loops deleted (`Trim.lean`), and then build
the line digraph of prop:arcdisjoint or prop:edgedisjoint on the trimmed multigraph.  The
guillotine table of `thm_main` on the reduced instance decides the problem.  As in lem:time
there is no machine model: running time is stated as the work of the table (DEVIATIONS item 20).
-/
import DSPP.EdgeDisjoint
import DSPP.Trim
import DSPP.Main
import DSPP.Extraction

open Classical

namespace DSPP

variable {V E : Type*}

/-- `N^e ≤ (3k)^e n^{2e}` when `N ≤ k n² + 2k` and `n ≥ 1`. -/
theorem pow_le_of_le_sq {N n k : ℕ} (e : ℕ) (hn : 1 ≤ n) (hN : N ≤ k * n ^ 2 + 2 * k) :
    N ^ e ≤ (3 * k) ^ e * n ^ (2 * e) := by
  have h1 : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ hn
  have h2 : N ≤ 3 * k * n ^ 2 := by nlinarith
  calc N ^ e ≤ (3 * k * n ^ 2) ^ e := Nat.pow_le_pow_left h2 e
    _ = (3 * k) ^ e * n ^ (2 * e) := by rw [mul_pow, pow_mul]

/-! ### Directed: trimming and the reduced instance -/

section Arc

variable [Fintype E] [DecidableEq E] (src tgt : E → V) (len : E → ℝ) (hpos : ∀ e, 0 < len e)
  (k : ℕ)

/-- The arcs kept by the trimming of cor:edgedisjoint: no loops, and at most `k` arcs of
minimum length from `u` to `v` for every ordered pair `(u, v)`. -/
def arcKept : E → Prop :=
  (MGraph.ofArcs src tgt len hpos).Kept (fun e => (src e, tgt e)) (fun p => p.1 = p.2) k

/-- The trimmed digraph. -/
def arcTrim : MGraph V {e // arcKept src tgt len hpos k e} :=
  MGraph.ofArcs (fun e => src e.1) (fun e => tgt e.1) (fun e => len e.1) (fun e => hpos e.1)

/-- Trimming the arcs does not change the answer of the arc-disjoint problem. -/
theorem arc_trim_iff (hk : 1 ≤ k) (s t : Fin k → V) :
    (MGraph.ofArcs src tgt len hpos).HasEdgeSolution s t ↔
      (arcTrim src tgt len hpos k).HasEdgeSolution s t :=
  MGraph.hasEdgeSolution_trim_iff (MGraph.ofArcs src tgt len hpos)
    (pr := fun e => (src e, tgt e)) (loopP := fun p => p.1 = p.2)
    (fun h hf => by
      simp only [Prod.mk.injEq] at hf
      exact ⟨hf.1.trans h.1, hf.2.trans h.2⟩)
    (fun h hl => h.1.symm.trans (hl.trans h.2)) s t hk

/-- The trimmed digraph has at most `k n (n-1)` arcs. -/
theorem card_arcKept_le [Fintype V] [DecidableEq V] :
    Fintype.card {e // arcKept src tgt len hpos k e} ≤
      k * (Fintype.card V * Fintype.card V - Fintype.card V) := by
  rw [Fintype.card_subtype]
  refine ((MGraph.ofArcs src tgt len hpos).card_kept_le (pr := fun e => (src e, tgt e))
    (loopP := fun p => p.1 = p.2) k).trans (le_of_eq ?_)
  congr 1
  rw [← Finset.card_univ, ← Finset.offDiag_card]
  congr 1
  ext p
  simp [Finset.mem_offDiag]

/-- The reduced instance of cor:edgedisjoint (i): the line digraph of prop:arcdisjoint on the
trimmed digraph. -/
noncomputable def arcReduced (hk : 2 ≤ k) (s t : Fin k → V) :
    Instance ({e // arcKept src tgt len hpos k e} ⊕ (Fin k ⊕ Fin k)) k :=
  (arcLine (fun e : {e // arcKept src tgt len hpos k e} => src e.1) (fun e => tgt e.1)
    (fun e => len e.1) (fun e => hpos e.1) s t).inst hk

end Arc

/-! ### Undirected: trimming and the reduced instance -/

section Edge

variable [Fintype E] [DecidableEq E] (fst snd : E → V) (len : E → ℝ) (hpos : ∀ e, 0 < len e)
  (k : ℕ)

/-- The edges kept by the trimming of cor:edgedisjoint: no loops, and at most `k` edges of
minimum length between `u` and `v` for every unordered pair `{u, v}`. -/
def edgeKept : E → Prop :=
  (MGraph.ofEdges fst snd len hpos).Kept (fun e => s(fst e, snd e)) Sym2.IsDiag k

/-- The trimmed graph. -/
def edgeTrim : MGraph V {e // edgeKept fst snd len hpos k e} :=
  MGraph.ofEdges (fun e => fst e.1) (fun e => snd e.1) (fun e => len e.1) (fun e => hpos e.1)

omit [Fintype E] [DecidableEq E] in
/-- Edges with the same ends join the same vertices. -/
theorem edge_hsub {u w : V} {e f : E} (h : (MGraph.ofEdges fst snd len hpos).step u e w)
    (hf : s(fst f, snd f) = s(fst e, snd e)) : (MGraph.ofEdges fst snd len hpos).step u f w := by
  rcases Sym2.eq_iff.1 hf with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases h with ⟨h3, h4⟩ | ⟨h3, h4⟩
  · exact Or.inl ⟨h1.trans h3, h2.trans h4⟩
  · exact Or.inr ⟨h1.trans h3, h2.trans h4⟩
  · exact Or.inr ⟨h1.trans h4, h2.trans h3⟩
  · exact Or.inl ⟨h1.trans h4, h2.trans h3⟩

omit [Fintype E] [DecidableEq E] in
/-- A loop joins a vertex to itself. -/
theorem edge_hloop {u w : V} {e : E} (h : (MGraph.ofEdges fst snd len hpos).step u e w)
    (hl : Sym2.IsDiag s(fst e, snd e)) : u = w := by
  have hd : fst e = snd e := Sym2.mk_isDiag_iff.1 hl
  rcases h with ⟨h3, h4⟩ | ⟨h3, h4⟩
  · rw [← h3, ← h4, hd]
  · rw [← h3, ← h4, hd]

/-- Trimming the edges does not change the answer of the edge-disjoint problem. -/
theorem edge_trim_iff (hk : 1 ≤ k) (s t : Fin k → V) :
    (MGraph.ofEdges fst snd len hpos).HasEdgeSolution s t ↔
      (edgeTrim fst snd len hpos k).HasEdgeSolution s t :=
  MGraph.hasEdgeSolution_trim_iff (MGraph.ofEdges fst snd len hpos)
    (pr := fun e => s(fst e, snd e)) (loopP := Sym2.IsDiag)
    (edge_hsub fst snd len hpos) (edge_hloop fst snd len hpos) s t hk

/-- The trimmed graph has at most `k (n choose 2)` edges. -/
theorem card_edgeKept_le [Fintype V] [DecidableEq V] :
    Fintype.card {e // edgeKept fst snd len hpos k e} ≤ k * (Fintype.card V).choose 2 := by
  rw [Fintype.card_subtype]
  refine ((MGraph.ofEdges fst snd len hpos).card_kept_le (pr := fun e => s(fst e, snd e))
    (loopP := Sym2.IsDiag) k).trans (le_of_eq ?_)
  congr 1
  rw [← Sym2.card_subtype_not_diag, Fintype.card_subtype]
  congr 1
  ext p
  simp

/-- The reduced instance of cor:edgedisjoint (ii): the digraph of prop:edgedisjoint on the
trimmed graph. -/
noncomputable def edgeReduced (hk : 2 ≤ k) (s t : Fin k → V) :
    Instance ({e // edgeKept fst snd len hpos k e} ⊕ (Fin k ⊕ Fin k)) k :=
  (edgeLine (fun e : {e // edgeKept fst snd len hpos k e} => fst e.1) (fun e => snd e.1)
    (fun e => len e.1) (fun e => hpos e.1) s t).inst hk

end Edge

/-- cor:edgedisjoint.  For `k ≥ 2` pairs with `s_i ≠ t_i` (terminals of different pairs may
coincide) and positive lengths, with parallel arcs or edges allowed:
(i) the arc-disjoint version in a digraph with `n` vertices and
(ii) the edge-disjoint version in an undirected graph with `n` vertices
are decided by the guillotine table on the reduced instance (`arcReduced`, `edgeReduced`).  The
reduced instance has at most `k n² + 2k` vertices, the work of the table is at most
`f(k) N^{6k²-4k-1}` for its number `N` of vertices, and at most `g(k) n^{2(6k²-4k-1)}`. -/
theorem cor_edgedisjoint :
    ∃ f g : ℕ → ℕ,
    (∀ (k : ℕ) [NeZero k] (hk : 2 ≤ k) (V E : Type) [Fintype V] [DecidableEq V] [Fintype E]
      [DecidableEq E] (src tgt : E → V) (len : E → ℝ) (hpos : ∀ e, 0 < len e)
      (s t : Fin k → V), (∀ i, s i ≠ t i) →
      ((arcReduced src tgt len hpos k hk s t).Tab Finset.univ
          (arcReduced src tgt len hpos k hk s t).Pi0 ↔
        (MGraph.ofArcs src tgt len hpos).HasEdgeSolution s t) ∧
      Fintype.card ({e // arcKept src tgt len hpos k e} ⊕ (Fin k ⊕ Fin k)) ≤
        k * Fintype.card V ^ 2 + 2 * k ∧
      (arcReduced src tgt len hpos k hk s t).splitWork +
          (arcReduced src tgt len hpos k hk s t).leafWork ≤
        f k * Fintype.card ({e // arcKept src tgt len hpos k e} ⊕ (Fin k ⊕ Fin k)) ^
          (6 * k ^ 2 - 4 * k - 1) ∧
      (arcReduced src tgt len hpos k hk s t).splitWork +
          (arcReduced src tgt len hpos k hk s t).leafWork ≤
        g k * Fintype.card V ^ (2 * (6 * k ^ 2 - 4 * k - 1))) ∧
    (∀ (k : ℕ) [NeZero k] (hk : 2 ≤ k) (V E : Type) [Fintype V] [DecidableEq V] [Fintype E]
      [DecidableEq E] (fst snd : E → V) (len : E → ℝ) (hpos : ∀ e, 0 < len e)
      (s t : Fin k → V), (∀ i, s i ≠ t i) →
      ((edgeReduced fst snd len hpos k hk s t).Tab Finset.univ
          (edgeReduced fst snd len hpos k hk s t).Pi0 ↔
        (MGraph.ofEdges fst snd len hpos).HasEdgeSolution s t) ∧
      Fintype.card ({e // edgeKept fst snd len hpos k e} ⊕ (Fin k ⊕ Fin k)) ≤
        k * Fintype.card V ^ 2 + 2 * k ∧
      (edgeReduced fst snd len hpos k hk s t).splitWork +
          (edgeReduced fst snd len hpos k hk s t).leafWork ≤
        f k * Fintype.card ({e // edgeKept fst snd len hpos k e} ⊕ (Fin k ⊕ Fin k)) ^
          (6 * k ^ 2 - 4 * k - 1) ∧
      (edgeReduced fst snd len hpos k hk s t).splitWork +
          (edgeReduced fst snd len hpos k hk s t).leafWork ≤
        g k * Fintype.card V ^ (2 * (6 * k ^ 2 - 4 * k - 1))) := by
  obtain ⟨hcor, ⟨f, hf⟩, -⟩ := thm_main
  refine ⟨f, fun k => f k * (3 * k) ^ (6 * k ^ 2 - 4 * k - 1), ?_, ?_⟩
  · intro k _ hk V E _ _ _ _ src tgt len hpos s t hst
    have hn : 1 ≤ Fintype.card V := Fintype.card_pos_iff.2 ⟨s ⟨0, by omega⟩⟩
    have hN : Fintype.card ({e // arcKept src tgt len hpos k e} ⊕ (Fin k ⊕ Fin k)) ≤
        k * Fintype.card V ^ 2 + 2 * k := by
      rw [LineData.card_vertices]
      have := card_arcKept_le src tgt len hpos k (V := V)
      have h2 : Fintype.card V * Fintype.card V - Fintype.card V ≤ Fintype.card V ^ 2 := by
        rw [sq]; exact Nat.sub_le _ _
      nlinarith
    have hw := hf k _ (arcReduced src tgt len hpos k hk s t)
    refine ⟨?_, hN, hw, ?_⟩
    · rw [hcor k _ (arcReduced src tgt len hpos k hk s t), arc_trim_iff src tgt len hpos k
        (by omega) s t]
      exact ((prop_arcdisjoint (fun e : {e // arcKept src tgt len hpos k e} => src e.1)
        (fun e => tgt e.1) (fun e => len e.1) (fun e => hpos e.1) s t hk hst).1.1).symm
    · refine hw.trans ?_
      rw [mul_assoc]
      exact Nat.mul_le_mul_left _ (pow_le_of_le_sq _ hn hN)
  · intro k _ hk V E _ _ _ _ fst snd len hpos s t hst
    have hn : 1 ≤ Fintype.card V := Fintype.card_pos_iff.2 ⟨s ⟨0, by omega⟩⟩
    have hN : Fintype.card ({e // edgeKept fst snd len hpos k e} ⊕ (Fin k ⊕ Fin k)) ≤
        k * Fintype.card V ^ 2 + 2 * k := by
      rw [LineData.card_vertices]
      have := card_edgeKept_le fst snd len hpos k (V := V)
      have h2 : (Fintype.card V).choose 2 ≤ Fintype.card V ^ 2 := by
        rw [Nat.choose_two_right, sq]; exact Nat.div_le_of_le_mul (by
          have := Nat.sub_le (Fintype.card V) 1
          nlinarith)
      nlinarith
    have hw := hf k _ (edgeReduced fst snd len hpos k hk s t)
    refine ⟨?_, hN, hw, ?_⟩
    · rw [hcor k _ (edgeReduced fst snd len hpos k hk s t), edge_trim_iff fst snd len hpos k
        (by omega) s t]
      exact ((prop_edgedisjoint (fun e : {e // edgeKept fst snd len hpos k e} => fst e.1)
        (fun e => snd e.1) (fun e => len e.1) (fun e => hpos e.1) s t hk hst).1.1).symm
    · refine hw.trans ?_
      rw [mul_assoc]
      exact Nat.mul_le_mul_left _ (pow_le_of_le_sq _ hn hN)


/-! ### Output of a solution -/

section ArcBack

variable [Fintype E] [DecidableEq E] (src tgt : E → V) (len : E → ℝ) (hpos : ∀ e, 0 < len e)
  (k : ℕ)

/-- The arc-disjoint paths of the digraph read off a solution `Q` of the reduced instance
`arcReduced`: the paths `LineData.backSol` of the trimmed digraph, with their arcs read as arcs
of the digraph. -/
noncomputable def arcBack (s t : Fin k → V)
    (Q : Fin k → List ({e // arcKept src tgt len hpos k e} ⊕ (Fin k ⊕ Fin k))) :
    Fin k → List (E × V) :=
  fun i => (LineData.backSol (arcTrim src tgt len hpos k) s t Q i).map (Prod.map Subtype.val id)

/-- `arcBack` maps every solution of `arcReduced` to `k` pairwise arc-disjoint shortest paths of
the digraph. -/
theorem isEdgeSolution_arcBack (hk : 2 ≤ k) (s t : Fin k → V) (hst : ∀ i, s i ≠ t i)
    (Q : Fin k → List ({e // arcKept src tgt len hpos k e} ⊕ (Fin k ⊕ Fin k)))
    (hQ : (arcReduced src tgt len hpos k hk s t).IsSolution Q) :
    (MGraph.ofArcs src tgt len hpos).IsEdgeSolution s t (arcBack src tgt len hpos k s t Q) :=
  MGraph.isEdgeSolution_of_trim (MGraph.ofArcs src tgt len hpos)
    (pr := fun e => (src e, tgt e)) (loopP := fun p => p.1 = p.2)
    (fun h hf => by
      simp only [Prod.mk.injEq] at hf
      exact ⟨hf.1.trans h.1, hf.2.trans h.2⟩)
    (fun h hl => h.1.symm.trans (hl.trans h.2)) s t (by omega)
    ((prop_arcdisjoint (fun e : {e // arcKept src tgt len hpos k e} => src e.1)
      (fun e => tgt e.1) (fun e => len e.1) (fun e => hpos e.1) s t hk hst).1.2 Q hQ)

end ArcBack

section EdgeBack

variable [Fintype E] [DecidableEq E] (fst snd : E → V) (len : E → ℝ) (hpos : ∀ e, 0 < len e)
  (k : ℕ)

/-- The edge-disjoint paths of the graph read off a solution `Q` of the reduced instance
`edgeReduced`: the paths `LineData.backSol` of the trimmed graph, with their edges read as edges
of the graph. -/
noncomputable def edgeBack (s t : Fin k → V)
    (Q : Fin k → List ({e // edgeKept fst snd len hpos k e} ⊕ (Fin k ⊕ Fin k))) :
    Fin k → List (E × V) :=
  fun i => (LineData.backSol (edgeTrim fst snd len hpos k) s t Q i).map (Prod.map Subtype.val id)

/-- `edgeBack` maps every solution of `edgeReduced` to `k` pairwise edge-disjoint shortest paths
of the graph. -/
theorem isEdgeSolution_edgeBack (hk : 2 ≤ k) (s t : Fin k → V) (hst : ∀ i, s i ≠ t i)
    (Q : Fin k → List ({e // edgeKept fst snd len hpos k e} ⊕ (Fin k ⊕ Fin k)))
    (hQ : (edgeReduced fst snd len hpos k hk s t).IsSolution Q) :
    (MGraph.ofEdges fst snd len hpos).IsEdgeSolution s t (edgeBack fst snd len hpos k s t Q) :=
  MGraph.isEdgeSolution_of_trim (MGraph.ofEdges fst snd len hpos)
    (pr := fun e => s(fst e, snd e)) (loopP := Sym2.IsDiag)
    (edge_hsub fst snd len hpos) (edge_hloop fst snd len hpos) s t (by omega)
    ((prop_edgedisjoint (fun e : {e // edgeKept fst snd len hpos k e} => fst e.1)
      (fun e => snd e.1) (fun e => len e.1) (fun e => hpos e.1) s t hk hst).1.2 Q hQ)

end EdgeBack

/-- cor:edgedisjoint, "find one if it exists".  If the root entry of the guillotine table on the
reduced instance is true, then the paths that the table outputs (`Instance.solution`), mapped
back by `arcBack` (`edgeBack`), are `k` pairwise arc-disjoint (edge-disjoint) shortest paths of
the digraph (graph). -/
theorem cor_edgedisjoint_solution :
    (∀ (k : ℕ) [NeZero k] (hk : 2 ≤ k) (V E : Type) [Fintype V] [DecidableEq V] [Fintype E]
      [DecidableEq E] (src tgt : E → V) (len : E → ℝ) (hpos : ∀ e, 0 < len e)
      (s t : Fin k → V), (∀ i, s i ≠ t i) →
      (arcReduced src tgt len hpos k hk s t).Tab Finset.univ
          (arcReduced src tgt len hpos k hk s t).Pi0 →
      (MGraph.ofArcs src tgt len hpos).IsEdgeSolution s t
        (arcBack src tgt len hpos k s t (arcReduced src tgt len hpos k hk s t).solution)) ∧
    (∀ (k : ℕ) [NeZero k] (hk : 2 ≤ k) (V E : Type) [Fintype V] [DecidableEq V] [Fintype E]
      [DecidableEq E] (fst snd : E → V) (len : E → ℝ) (hpos : ∀ e, 0 < len e)
      (s t : Fin k → V), (∀ i, s i ≠ t i) →
      (edgeReduced fst snd len hpos k hk s t).Tab Finset.univ
          (edgeReduced fst snd len hpos k hk s t).Pi0 →
      (MGraph.ofEdges fst snd len hpos).IsEdgeSolution s t
        (edgeBack fst snd len hpos k s t (edgeReduced fst snd len hpos k hk s t).solution)) :=
  ⟨fun k _ hk _ _ _ _ _ _ src tgt len hpos s t hst h =>
      isEdgeSolution_arcBack src tgt len hpos k hk s t hst _
        ((arcReduced src tgt len hpos k hk s t).extract_isSolution h),
    fun k _ hk _ _ _ _ _ _ fst snd len hpos s t hst h =>
      isEdgeSolution_edgeBack fst snd len hpos k hk s t hst _
        ((edgeReduced fst snd len hpos k hk s t).extract_isSolution h)⟩

end DSPP
