/-
lem:pebbling: the leaf rule decides `S(U, Π)` inside a point class.

Paper: "Directed k Disjoint Shortest Paths Is Polynomial for Every Fixed k" (Saeed Amiri),
Section "The algorithm", subsection "The leaf rule: pebbling inside a point class".
-/
import DSPP.Table

open Classical

namespace DSPP

variable {k : ℕ} [NeZero k] {V : Type*} [Fintype V] [DecidableEq V]

/-- A chain whose elements all satisfy `p` is a chain for the relation strengthened by `p`. -/
theorem chain_strengthen {α : Type*} (p : α → Prop) (R : α → α → Prop) :
    ∀ l : List α, l.IsChain R → (∀ v ∈ l, p v) → l.IsChain (fun u w => p u ∧ p w ∧ R u w)
  | [], _, _ => List.isChain_nil
  | [_], _, _ => List.isChain_singleton _
  | a :: b :: l, h, hp => by
    rw [List.isChain_cons_cons] at h ⊢
    exact ⟨⟨hp a (by simp), hp b (by simp), h.1⟩,
      chain_strengthen p R (b :: l) h.2 (fun v hv => hp v (List.mem_cons_of_mem _ hv))⟩

/-- If the head satisfies `p` and every step of a chain stays in `p`, all elements satisfy `p`. -/
theorem chain_mem {α : Type*} (p : α → Prop) (R : α → α → Prop) :
    ∀ l : List α, l.IsChain (fun u w => p u ∧ p w ∧ R u w) → (∀ v, l.head? = some v → p v) →
      ∀ v ∈ l, p v
  | [], _, _, v, hv => by simp at hv
  | [a], _, hh, v, hv => by
    rw [List.mem_singleton] at hv
    exact hv ▸ hh a rfl
  | a :: b :: l, h, hh, v, hv => by
    rw [List.isChain_cons_cons] at h
    rcases List.mem_cons.1 hv with rfl | hv
    · exact hh v rfl
    · exact chain_mem p R (b :: l) h.2 (fun w hw => by
        simp only [List.head?_cons, Option.some.injEq] at hw
        exact hw ▸ h.1.2.1) v hv

namespace Instance

variable (G : Instance V k)


theorem key_lt_of_inD {U : Finset V} (hU : G.IsPointClass U) {u w : V} (hu : u ∈ U) (hw : w ∈ U) {l : Fin k}
    (h : G.inD l u w) : G.key u < G.key w := by
  obtain ⟨v, rfl⟩ := hU
  simp only [pointClass, Finset.mem_filter, Finset.mem_univ, true_and] at hu hw
  have hc : G.SameClass u w := fun i j => (hu i j).symm.trans (hw i j)
  have h0 := (G.lem_W2 h hc).2 0
  have hlen := (G.lem_W2 h hc).1
  have hlt : G.F 0 u < G.F 0 w := by linarith
  exact Prod.Lex.toLex_lt_toLex.2 (Or.inl hlt)

/-- lem:pebbling.  Let `U` be a point class and `Π` a set of demands with ends in `U`.  Then
the pebble game wins if and only if `S(U, Π)` holds.  (The running time `O(p n^{p+1})` is the
size of the game graph, `Pebble.card_states` and `Pebble.card_moves_le`.) -/
theorem lem_pebbling (U : Finset V) (hU : G.IsPointClass U) (Dm : Finset (Demand V k))
    (hends : ∀ δ ∈ Dm, δ.2.1 ∈ U ∧ δ.2.2 ∈ U) :
    G.pebbleWins U Dm ↔ G.Sem U Dm := by
  unfold pebbleWins
  rw [Pebble.fhw _ _ _ _ G.key_injective (fun r u w h => G.key_lt_of_inD hU h.1 h.2.1 h.2.2)]
  constructor
  · rintro ⟨P, hP, hdis⟩
    refine ⟨fun δ => if h : δ ∈ Dm then P ⟨δ, h⟩ else [], ?_, ?_⟩
    · intro δ hδ
      have := hP ⟨δ, hδ⟩
      simp only [dif_pos hδ]
      refine ⟨this.1, this.2.1, this.2.2.2, ?_, ?_⟩
      · exact chain_mem (· ∈ U) (G.inD δ.1) _ this.2.2.1
          (fun v hv => by rw [this.1] at hv; cases hv; exact (hends δ hδ).1) 
      · exact this.2.2.1.imp (fun _ _ h => h.2.2)
    · intro δ hδ δ' hδ' hne v hv hv'
      simp only [dif_pos hδ, dif_pos hδ'] at hv hv'
      exact hdis ⟨δ, hδ⟩ ⟨δ', hδ'⟩ (fun e => hne (congrArg Subtype.val e)) v hv hv'
  · rintro ⟨R, hR, hdis⟩
    refine ⟨fun r => R r.1, fun r => ?_, ?_⟩
    · obtain ⟨h1, h2, h3, h4, h5⟩ := hR r.1 r.2
      exact ⟨h1, h2, chain_strengthen (· ∈ U) (G.inD r.1.1) _ h5 h4, h3⟩
    · intro r r' hne v hv hv'
      exact hdis r.1 r.2 r'.1 r'.2 (fun e => hne (Subtype.ext e)) v hv hv'

/-- The leaf paths of lem:pebbling: if the pebble game for `Π` in `U` is won, the path for
`δ ∈ Π` is the trajectory of the pebble `δ` in the chosen winning play. -/
noncomputable def leafPaths (U : Finset V) (Dm : Finset (Demand V k)) (δ : Demand V k) :
    List V :=
  if h : G.pebbleWins U Dm ∧ δ ∈ Dm then
    Pebble.playPaths (fun r : {δ // δ ∈ Dm} => r.1.2.1) (fun r => r.1.2.2)
      (Pebble.play (fun r u w => u ∈ U ∧ w ∈ U ∧ G.inD r.1.1 u w) G.key
        (fun r : {δ // δ ∈ Dm} => r.1.2.1) (fun r => r.1.2.2) h.1) ⟨δ, h.2⟩
  else []

/-- lem:pebbling with explicit paths: in a point class, a won pebble game gives the paths
`leafPaths` for `S(U, Π)`. -/
theorem leafPaths_semBy (U : Finset V) (hU : G.IsPointClass U) (Dm : Finset (Demand V k))
    (hends : ∀ δ ∈ Dm, δ.2.1 ∈ U ∧ δ.2.2 ∈ U) (h : G.pebbleWins U Dm) :
    G.SemBy U Dm (G.leafPaths U Dm) := by
  obtain ⟨hP, hdis⟩ := Pebble.fhw_win (ι := {δ // δ ∈ Dm})
    (fun r u w => u ∈ U ∧ w ∈ U ∧ G.inD r.1.1 u w) G.key (fun r => r.1.2.1) (fun r => r.1.2.2)
    G.key_injective (fun r u w h => G.key_lt_of_inD hU h.1 h.2.1 h.2.2) h
  have hL : ∀ δ (hδ : δ ∈ Dm), G.leafPaths U Dm δ =
      Pebble.playPaths (fun r : {δ // δ ∈ Dm} => r.1.2.1) (fun r => r.1.2.2)
        (Pebble.play (fun r u w => u ∈ U ∧ w ∈ U ∧ G.inD r.1.1 u w) G.key
          (fun r : {δ // δ ∈ Dm} => r.1.2.1) (fun r => r.1.2.2) h) ⟨δ, hδ⟩ := by
    intro δ hδ
    unfold leafPaths
    rw [dif_pos ⟨h, hδ⟩]
  refine ⟨fun δ hδ => ?_, fun δ hδ δ' hδ' hne v hv hv' => ?_⟩
  · have := hP ⟨δ, hδ⟩
    rw [hL δ hδ]
    refine ⟨this.1, this.2.1, this.2.2.2, ?_, ?_⟩
    · exact chain_mem (· ∈ U) (G.inD δ.1) _ this.2.2.1
        (fun v hv => by rw [this.1] at hv; cases hv; exact (hends δ hδ).1)
    · exact this.2.2.1.imp (fun _ _ h => h.2.2)
  · rw [hL δ hδ] at hv
    rw [hL δ' hδ'] at hv'
    exact hdis ⟨δ, hδ⟩ ⟨δ', hδ'⟩ (fun e => hne (congrArg Subtype.val e)) v hv hv'

end Instance

end DSPP
