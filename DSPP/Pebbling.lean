/-
The pebble game of Fortune, Hopcroft and Wyllie on acyclic relations (the argument of
lem:pebbling), in a general form independent of the shortest-paths setting.

Paper: "Directed k Disjoint Shortest Paths Is Polynomial for Every Fixed k" (Saeed Amiri),
Section "The algorithm", subsection "The leaf rule: pebbling inside a point class".

Setting: pebbles `r : ι`, pebble `r` moves along the relation `E r` on `W`; every arc of every
`E r` increases `key`, an injective map into a linear order (the total order `≺` of the paper).
-/
import Mathlib

open Classical

namespace DSPP

namespace Pebble

variable {ι W κ : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder κ]
variable (E : ι → W → W → Prop) (key : W → κ) (a b : ι → W)

/-- One move of the game from the state `x` to the state `y`: the unfinished pebble `r`
(`x r ≠ b r`) whose position is `≺`-smallest among the unfinished pebbles moves along an arc of
`E r` to a vertex not occupied by another pebble. -/
def Move (x y : ι → W) : Prop :=
  ∃ r, x r ≠ b r ∧ (∀ r', x r' ≠ b r' → key (x r) ≤ key (x r')) ∧
    ∃ w, E r (x r) w ∧ (∀ r', r' ≠ r → x r' ≠ w) ∧ y = Function.update x r w

/-- The game is won: the start `a` is a state (pairwise distinct positions), and the goal `b`
is reachable from `a` by moves. -/
def Wins : Prop := Function.Injective a ∧ Relation.ReflTransGen (Move E key b) a b

/-- Pairwise vertex-disjoint paths: `P r` leads from `a r` to `b r` along arcs of `E r`. -/
def DisjointPaths : Prop :=
  ∃ P : ι → List W,
    (∀ r, (P r).head? = some (a r) ∧ (P r).getLast? = some (b r) ∧
      (P r).IsChain (E r) ∧ (P r).Nodup) ∧
    ∀ r r', r ≠ r' → ∀ w ∈ P r, w ∉ P r'

/-! ### Paths give a winning play -/

theorem reach_aux (n : ℕ) :
    ∀ (x : ι → W) (T : ι → List W), ∑ r, (T r).length = n →
      (∀ r, (x r :: T r).IsChain (E r)) → (∀ r, (x r :: T r).Nodup) →
      (∀ r r', r ≠ r' → ∀ v ∈ x r :: T r, v ∉ x r' :: T r') →
      (∀ r, (x r :: T r).getLast? = some (b r)) →
      Relation.ReflTransGen (Move E key b) x b := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x T hn hch hnd hdis hlast
    by_cases hu : ∃ r, x r ≠ b r
    · obtain ⟨r0, hr0⟩ := hu
      obtain ⟨r, hr, hmin⟩ := Finset.exists_min_image
        (Finset.univ.filter fun r => x r ≠ b r) (fun r => key (x r)) ⟨r0, by simp [hr0]⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr hmin
      have hTr : T r ≠ [] := by
        intro h
        have := hlast r
        rw [h] at this
        simp at this
        exact hr this
      obtain ⟨w, T', hT⟩ := List.exists_cons_of_ne_nil hTr
      have hch' := hch r
      rw [hT] at hch'
      rw [List.isChain_cons_cons] at hch'
      have hnd' := hnd r
      rw [hT] at hnd'
      have hsub : ∀ v ∈ w :: T', v ∈ x r :: T r := by
        intro v hv
        rw [hT]
        exact List.mem_cons_of_mem _ hv
      refine Relation.ReflTransGen.head
        (b := Function.update x r w) ?_
        (ih (∑ r', (Function.update T r T' r').length) ?_ (Function.update x r w)
          (Function.update T r T') rfl ?_ ?_ ?_ ?_)
      · refine ⟨r, hr, fun r' hr' => hmin r' hr', w, hch'.1, ?_, rfl⟩
        intro r' hne hx
        exact hdis r r' hne.symm w (hsub w (List.mem_cons_self ..)) (hx ▸ List.mem_cons_self ..)
      · rw [← hn]
        apply Finset.sum_lt_sum
        · intro r'
          by_cases h : r' = r
          · subst h
            simp [hT]
          · simp [Function.update_of_ne h]
        · refine ⟨r, Finset.mem_univ _, ?_⟩
          simp [hT]
      · intro r'
        by_cases h : r' = r
        · subst h; simpa using hch'.2
        · simpa [Function.update_of_ne h] using hch r'
      · intro r'
        by_cases h : r' = r
        · subst h; simpa using hnd'.of_cons
        · simpa [Function.update_of_ne h] using hnd r'
      · intro r1 r2 hne v hv hv2
        have key1 : ∀ r', ∀ v, v ∈ Function.update x r w r' :: Function.update T r T' r' →
            v ∈ x r' :: T r' := by
          intro r' v hv
          by_cases h : r' = r
          · subst h
            simp only [Function.update_self] at hv
            exact hsub v hv
          · simpa [Function.update_of_ne h] using hv
        exact hdis r1 r2 hne v (key1 r1 v hv) (key1 r2 v hv2)
      · intro r'
        by_cases h : r' = r
        · subst h
          simp only [Function.update_self]
          have := hlast r'
          rw [hT, List.getLast?_cons_cons] at this
          exact this
        · simpa [Function.update_of_ne h] using hlast r'
    · have : x = b := funext fun r => not_not.1 (not_exists.1 hu r)
      subst this
      exact Relation.ReflTransGen.refl
/-! ### A winning play gives paths -/

/-- Invariant of a play from `a`: `x` is the current state and `x r :: rest r` the trajectory of
pebble `r`, newest vertex first. -/
def Inv (x : ι → W) (rest : ι → List W) : Prop :=
  (∀ r, (x r :: rest r).IsChain (fun p q => E r q p)) ∧
  (∀ r, (x r :: rest r).getLast? = some (a r)) ∧
  (∀ r r', r ≠ r' → ∀ v ∈ x r :: rest r, v ∉ x r' :: rest r') ∧
  (∀ r r', r ≠ r' → ∀ v ∈ rest r, x r' = b r' ∨ key v < key (x r'))

theorem Inv_step (hkey : Function.Injective key) (hE : ∀ r u v, E r u v → key u < key v)
    {x y : ι → W} {rest : ι → List W} (h : Inv E key a b x rest) (hm : Move E key b x y) :
    ∃ rest', Inv E key a b y rest' := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨r, hr, hmin, w, hxw, hfree, rfl⟩ := hm
  have hlt : key (x r) < key w := hE r _ _ hxw
  refine ⟨Function.update rest r (x r :: rest r), ?_, ?_, ?_, ?_⟩
  · intro r'
    by_cases h : r' = r
    · subst h
      simp only [Function.update_self]
      rw [List.isChain_cons_cons]
      exact ⟨hxw, h1 r'⟩
    · simpa [Function.update_of_ne h] using h1 r'
  · intro r'
    by_cases h : r' = r
    · subst h
      simp only [Function.update_self]
      rw [List.getLast?_cons_cons]
      exact h2 r'
    · simpa [Function.update_of_ne h] using h2 r'
  · -- disjointness
    have hw : ∀ r', r' ≠ r → w ∉ x r' :: rest r' := by
      intro r' hne hmem
      rcases List.mem_cons.1 hmem with h | h
      · exact hfree r' hne h.symm
      · rcases h4 r' r hne w h with h | h
        · exact hr h
        · exact absurd (lt_trans hlt h) (lt_irrefl _)
    intro r1 r2 hne v hv hv2
    by_cases h1' : r1 = r
    · subst h1'
      have hne2 : r2 ≠ r1 := hne.symm
      simp only [Function.update_self, Function.update_of_ne hne2] at hv hv2
      rcases List.mem_cons.1 hv with rfl | hv
      · exact hw r2 hne2 hv2
      · exact h3 r1 r2 hne v hv hv2
    · by_cases h2' : r2 = r
      · subst h2'
        simp only [Function.update_self, Function.update_of_ne h1'] at hv hv2
        rcases List.mem_cons.1 hv2 with rfl | hv2
        · exact hw r1 h1' hv
        · exact h3 r1 r2 hne v hv hv2
      · simp only [Function.update_of_ne h1', Function.update_of_ne h2'] at hv hv2
        exact h3 r1 r2 hne v hv hv2
  · intro r1 r2 hne v hv
    by_cases h1' : r1 = r
    · subst h1'
      have hne2 : r2 ≠ r1 := hne.symm
      simp only [Function.update_self, Function.update_of_ne hne2] at hv ⊢
      rcases List.mem_cons.1 hv with rfl | hv
      · by_cases hf : x r2 = b r2
        · exact Or.inl hf
        · right
          have hle := hmin r2 hf
          have hneq : key (x r1) ≠ key (x r2) := by
            intro e
            have := hkey e
            exact h3 r1 r2 hne _ (List.mem_cons_self ..) (this ▸ List.mem_cons_self ..)
          exact lt_of_le_of_ne hle hneq
      · exact h4 r1 r2 hne v hv
    · simp only [Function.update_of_ne h1'] at hv
      by_cases h2' : r2 = r
      · subst h2'
        simp only [Function.update_self]
        rcases h4 r1 r2 hne v hv with h | h
        · exact absurd h hr
        · exact Or.inr (lt_trans h hlt)
      · simp only [Function.update_of_ne h2']
        exact h4 r1 r2 hne v hv

theorem Inv_start (ha : Function.Injective a) : Inv E key a b a (fun _ => []) := by
  refine ⟨fun r => by simp, fun r => by simp, ?_, fun r r' _ v hv => by simp at hv⟩
  intro r r' hne v hv hv'
  simp only [List.mem_singleton] at hv hv'
  exact hne (ha (hv.symm.trans hv'))

theorem Inv_reach (hkey : Function.Injective key) (hE : ∀ r u v, E r u v → key u < key v)
    (ha : Function.Injective a) {x : ι → W}
    (h : Relation.ReflTransGen (Move E key b) a x) : ∃ rest, Inv E key a b x rest := by
  induction h with
  | refl => exact ⟨_, Inv_start E key a b ha⟩
  | tail _ hm ih =>
    obtain ⟨rest, hr⟩ := ih
    exact Inv_step E key a b hkey hE hr hm

/-- Fortune--Hopcroft--Wyllie (the argument of lem:pebbling): if every arc increases `key`,
the game is won if and only if there are pairwise disjoint paths. -/
theorem fhw (hkey : Function.Injective key) (hE : ∀ r u v, E r u v → key u < key v) :
    Wins E key a b ↔ DisjointPaths E a b := by
  constructor
  · rintro ⟨ha, hreach⟩
    obtain ⟨rest, h1, h2, h3, -⟩ := Inv_reach E key a b hkey hE ha hreach
    refine ⟨fun r => (b r :: rest r).reverse, fun r => ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [List.head?_reverse]; exact h2 r
    · rw [List.getLast?_reverse]; rfl
    · exact List.isChain_reverse.2 (h1 r)
    · rw [List.nodup_reverse]
      have hc := (h1 r).imp (fun {p q} (h : E r q p) => hE r q p h)
      have : IsTrans W (fun p q => key q < key p) := ⟨fun _ _ _ h1 h2 => lt_trans h2 h1⟩
      exact ((List.isChain_iff_pairwise.1 hc).imp fun {p q} (h : key q < key p) e => by
        subst e; exact lt_irrefl _ h)
    · intro r r' hne v hv hv'
      rw [List.mem_reverse] at hv hv'
      exact h3 r r' hne v hv hv'
  · rintro ⟨P, hP, hdis⟩
    have hPe : ∀ r, ∃ T, P r = a r :: T := fun r =>
      List.head?_eq_some_iff.1 (hP r).1
    choose T hT using hPe
    have ha : Function.Injective a := by
      intro r r' e
      by_contra hne
      refine hdis r r' hne (a r) ?_ ?_
      · rw [hT r]; exact List.mem_cons_self ..
      · rw [hT r', ← e]; exact List.mem_cons_self ..
    refine ⟨ha, reach_aux E key b _ a T rfl ?_ ?_ ?_ ?_⟩
    · intro r; rw [← hT r]; exact (hP r).2.2.1
    · intro r; rw [← hT r]; exact (hP r).2.2.2
    · intro r r' hne v hv hv'
      rw [← hT r] at hv; rw [← hT r'] at hv'
      exact hdis r r' hne v hv hv'
    · intro r; rw [← hT r]; exact (hP r).2.1

/-- Size of the game graph (lem:pebbling, running time): at most `|W|^{|ι|}` states. -/
theorem card_states [Fintype W] : Fintype.card (ι → W) = Fintype.card W ^ Fintype.card ι := by
  simp

/-- Size of the game graph (lem:pebbling, running time): from an injective state there are at
most `|W|` moves. -/
theorem card_moves_le [Fintype W] [DecidableEq W] (hkey : Function.Injective key) (x : ι → W)
    (hx : Function.Injective x) :
    (Finset.univ.filter fun y => Move E key b x y).card ≤ Fintype.card W := by
  by_cases hex : ∃ r, x r ≠ b r ∧ ∀ r', x r' ≠ b r' → key (x r) ≤ key (x r')
  · obtain ⟨r0, hr0, hmin0⟩ := hex
    have hsub : (Finset.univ.filter fun y => Move E key b x y) ⊆
        Finset.univ.image (fun w => Function.update x r0 w) := by
      intro y hy
      rw [Finset.mem_filter] at hy
      obtain ⟨r, hr, hmin, w, -, -, rfl⟩ := hy.2
      have hreq : r = r0 := by
        apply hx
        apply hkey
        exact le_antisymm (hmin r0 hr0) (hmin0 r hr)
      subst hreq
      exact Finset.mem_image.2 ⟨w, Finset.mem_univ _, rfl⟩
    exact (Finset.card_le_card hsub).trans
      (Finset.card_image_le.trans (by simp))
  · have : (Finset.univ.filter fun y => Move E key b x y) = ∅ := by
      apply Finset.filter_eq_empty_iff.2
      intro y _ hy
      obtain ⟨r, hr, hmin, -⟩ := hy
      exact hex ⟨r, hr, hmin⟩
    rw [this]
    simp

end Pebble

end DSPP
