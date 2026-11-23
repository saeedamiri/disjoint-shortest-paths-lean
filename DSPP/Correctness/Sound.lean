/-
Soundness of the table (lem:sound): helper lemmas.

Paper: "Directed k Disjoint Shortest Paths Is Polynomial for Every Fixed k" (Saeed Amiri),
Section "The algorithm", subsection "Correctness".

The split step: the paths of the sub-demands on the two sides are concatenated along the chains
with the interface arcs.  Soundness uses no property of the potentials.
-/
import DSPP.Leaf

open Classical

namespace DSPP

variable {k : ℕ} {V : Type*}

/-- The chain `(l, a_0, b_0), ..., (l, a_q, b_q)` of a demand `(l, a, b)` cut at the arcs
`e_1, ..., e_q`, written recursively. -/
def chainL (l : Fin k) : V → List (V × V) → V → List (Fin k × V × V)
  | a, [], b => [(l, a, b)]
  | a, e :: es, b => (l, a, e.1) :: chainL l e.2 es b

theorem chainL_eq_zip (l : Fin k) (a b : V) (es : List (V × V)) :
    (List.zip (a :: es.map Prod.snd) (es.map Prod.fst ++ [b])).map (fun p => (l, p.1, p.2)) =
      chainL l a es b := by
  induction es generalizing a with
  | nil => simp [chainL]
  | cons e es ih => simp [chainL, ← ih]

theorem label_of_mem_chainL {l : Fin k} {a b : V} {es : List (V × V)} {σ : Fin k × V × V}
    (h : σ ∈ chainL l a es b) : σ.1 = l := by
  induction es generalizing a with
  | nil => simp [chainL] at h; rw [h]
  | cons e es ih =>
    simp only [chainL, List.mem_cons] at h
    rcases h with rfl | h
    · rfl
    · exact ih h

/-- Concatenating the paths of a chain with the cutting arcs gives a walk from `a` to `b`. -/
theorem flatten_chainL (rel : V → V → Prop) (l : Fin k) (Rs : Fin k × V × V → List V) :
    ∀ (a : V) (es : List (V × V)) (b : V),
      (∀ σ ∈ chainL l a es b, (Rs σ).head? = some σ.2.1 ∧ (Rs σ).getLast? = some σ.2.2 ∧
        (Rs σ).IsChain rel) →
      (∀ e ∈ es, rel e.1 e.2) →
      ((chainL l a es b).map Rs).flatten.head? = some a ∧
        ((chainL l a es b).map Rs).flatten.getLast? = some b ∧
        ((chainL l a es b).map Rs).flatten.IsChain rel := by
  intro a es b
  induction es generalizing a with
  | nil =>
    intro h _
    simpa [chainL] using h (l, a, b) (by simp [chainL])
  | cons e es ih =>
    intro h he
    obtain ⟨h1, h2, h3⟩ := h (l, a, e.1) (by simp [chainL])
    obtain ⟨i1, i2, i3⟩ := ih e.2 (fun σ hσ => h σ (by simp [chainL, hσ]))
      (fun e' he' => he e' (List.mem_cons_of_mem _ he'))
    have hne : Rs (l, a, e.1) ≠ [] := by intro h0; simp [h0] at h1
    have hne' : ((chainL l e.2 es b).map Rs).flatten ≠ [] := by intro h0; simp [h0] at i1
    simp only [chainL, List.map_cons, List.flatten_cons]
    refine ⟨?_, ?_, ?_⟩
    · rw [List.head?_append_of_ne_nil _ hne]; exact h1
    · rw [List.getLast?_append_of_ne_nil _ hne']; exact i2
    · rw [List.isChain_append]
      refine ⟨h3, i3, ?_⟩
      intro x hx y hy
      simp only at h1 h2
      rw [h2] at hx; rw [i1] at hy
      simp only [Option.mem_def, Option.some.injEq] at hx hy
      subst hx hy
      exact he e (by simp)

variable [NeZero k] [Fintype V] [DecidableEq V]

namespace Instance

variable (G : Instance V k)

theorem uminus_uplus_disj {U : Finset V} {sp : StarIdx k × ℝ × ℝ} (hsp : sp ∈ G.splits U)
    {v : V} (hm : v ∈ G.Uminus U sp) (hp : v ∈ G.Uplus U sp) : False := by
  obtain ⟨-, -, hlt, -⟩ := G.isSplit_of_mem_splits hsp
  simp only [Uminus, Uplus, Finset.mem_filter] at hm hp
  linarith [hm.2, hp.2]

theorem mem_allSub_of_mem_PiMinus {U : Finset V} {Dm : Finset (Demand V k)}
    {sp : StarIdx k × ℝ × ℝ} {I : Finset (ArcDemand V k)} {σ : Demand V k}
    (h : σ ∈ G.PiMinus U Dm sp I) : σ ∈ G.allSub Dm I ∧ σ.2.1 ∈ G.Uminus U sp := by
  simpa [PiMinus, subMinus] using h

theorem mem_allSub_of_mem_PiPlus {U : Finset V} {Dm : Finset (Demand V k)}
    {sp : StarIdx k × ℝ × ℝ} {I : Finset (ArcDemand V k)} {σ : Demand V k}
    (h : σ ∈ G.PiPlus U Dm sp I) : σ ∈ G.allSub Dm I ∧ σ.2.1 ∈ G.Uplus U sp := by
  simpa [PiPlus, subPlus] using h

/-- The sub-demands of `Π⁻` have both ends in `U⁻`. -/
theorem ends_PiMinus {U : Finset V} {Dm : Finset (Demand V k)} {sp : StarIdx k × ℝ × ℝ}
    {I : Finset (ArcDemand V k)} (hsp : sp ∈ G.splits U) (hV : G.Valid U Dm sp I) :
    ∀ σ ∈ G.PiMinus U Dm sp I, σ.2.1 ∈ G.Uminus U sp ∧ σ.2.2 ∈ G.Uminus U sp := by
  intro σ hσ
  obtain ⟨h1, h2⟩ := G.mem_allSub_of_mem_PiMinus hσ
  rcases hV.2.1 σ h1 with h | h
  · exact h
  · exact (G.uminus_uplus_disj hsp h2 h.1).elim

/-- The sub-demands of `Π⁺` have both ends in `U⁺`. -/
theorem ends_PiPlus {U : Finset V} {Dm : Finset (Demand V k)} {sp : StarIdx k × ℝ × ℝ}
    {I : Finset (ArcDemand V k)} (hsp : sp ∈ G.splits U) (hV : G.Valid U Dm sp I) :
    ∀ σ ∈ G.PiPlus U Dm sp I, σ.2.1 ∈ G.Uplus U sp ∧ σ.2.2 ∈ G.Uplus U sp := by
  intro σ hσ
  obtain ⟨h1, h2⟩ := G.mem_allSub_of_mem_PiPlus hσ
  rcases hV.2.1 σ h1 with h | h
  · exact (G.uminus_uplus_disj hsp h.1 h2).elim
  · exact h

omit [NeZero k] [Fintype V] in
theorem demandEnds_ne_zero (σ : Demand V k) : demandEnds σ ≠ 0 := by
  unfold demandEnds; split_ifs <;> simp

omit [NeZero k] [Fintype V] in
/-- (V2) implies that the sub-demands are pairwise different: the multiset of all sub-demands
has no repetitions. -/
theorem nodup_of_nodup_bind_demandEnds {s : Multiset (Demand V k)}
    (h : (s.bind demandEnds).Nodup) : s.Nodup := by
  rw [Multiset.nodup_bind] at h
  obtain ⟨L, rfl, hL⟩ := h.2
  rw [Multiset.coe_nodup]
  refine hL.imp ?_
  intro a b hab hEq
  subst hEq
  obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero (demandEnds_ne_zero a)
  exact Multiset.disjoint_left.1 hab hx hx

omit [NeZero k] in
/-- From `allSub` without repetitions: every chain has no repetitions, and the chains of
different demands share no sub-demand. -/
theorem chain_nodup_disj {Dm : Finset (Demand V k)} {I : Finset (ArcDemand V k)}
    (h : (G.allSub Dm I).Nodup) :
    (∀ δ ∈ Dm, (G.chain I δ).Nodup) ∧
      ∀ δ ∈ Dm, ∀ δ' ∈ Dm, δ ≠ δ' → ∀ σ ∈ G.chain I δ, σ ∉ G.chain I δ' := by
  rw [allSub, Multiset.nodup_bind] at h
  refine ⟨fun δ hδ => by simpa using h.1 δ hδ, ?_⟩
  obtain ⟨L, hL, hpw⟩ := h.2
  intro δ hδ δ' hδ' hne σ hσ hσ'
  have hδL : δ ∈ L := by rw [← Multiset.mem_coe, ← hL]; exact hδ
  have hδL' : δ' ∈ L := by rw [← Multiset.mem_coe, ← hL]; exact hδ'
  have hsymm : ∀ a b : Demand V k,
      Function.onFun Disjoint (fun δ => (G.chain I δ : Multiset (Demand V k))) a b →
        Function.onFun Disjoint (fun δ => (G.chain I δ : Multiset (Demand V k))) b a := by
    intro a b hab
    simp only [Function.onFun] at hab ⊢
    exact hab.symm
  have : Std.Symm (Function.onFun Disjoint (fun δ => (G.chain I δ : Multiset (Demand V k)))) :=
    ⟨hsymm⟩
  have := hpw.forall hδL hδL' hne
  simp only [Function.onFun] at this
  exact Multiset.disjoint_left.1 this (by simpa using hσ) (by simpa using hσ')

omit [NeZero k] in
theorem chain_eq_chainL (I : Finset (ArcDemand V k)) (δ : Demand V k) :
    G.chain I δ = chainL δ.1 δ.2.1 (G.sortedArcs I δ) δ.2.2 := by
  rw [← chainL_eq_zip]; rfl

/-- The arcs of an interface assigned to `δ = (l, a, b)` are arcs of `D_l`. -/
theorem inD_of_mem_sortedArcs {U : Finset V} {Dm : Finset (Demand V k)}
    {sp : StarIdx k × ℝ × ℝ} {I : Finset (ArcDemand V k)} (hI : I ∈ G.interfaces U Dm sp)
    {δ : Demand V k} {e : V × V} (he : e ∈ G.sortedArcs I δ) : G.inD δ.1 e.1 e.2 := by
  unfold sortedArcs at he
  rw [(List.mergeSort_perm _ _).mem_iff, Finset.mem_toList, assigned, Finset.mem_image] at he
  obtain ⟨p, hp, rfl⟩ := he
  rw [Finset.mem_filter] at hp
  simp only [interfaces, Finset.mem_filter, Finset.mem_powerset] at hI
  have := hI.1 hp.1
  simp only [candPairs, Finset.mem_filter] at this
  rw [← hp.2]; exact this.2.1

/-- The split step of lem:sound: paths for `Π⁻` in `U⁻` and for `Π⁺` in `U⁺`, joined by the
interface arcs along the chains, are paths for `Π` in `U`. -/
theorem sound_split {U : Finset V} {Dm : Finset (Demand V k)} {sp : StarIdx k × ℝ × ℝ}
    {I : Finset (ArcDemand V k)} (hsp : sp ∈ G.splits U) (hI : I ∈ G.interfaces U Dm sp)
    (hV : G.Valid U Dm sp I) (hm : G.Sem (G.Uminus U sp) (G.PiMinus U Dm sp I))
    (hp : G.Sem (G.Uplus U sp) (G.PiPlus U Dm sp I)) : G.Sem U Dm := by
  obtain ⟨Rm, hRm, hRmd⟩ := hm
  obtain ⟨Rp, hRp, hRpd⟩ := hp
  let Rs : Demand V k → List V := fun σ =>
    if σ.2.1 ∈ G.Uminus U sp then Rm σ else Rp σ
  have hRs : ∀ σ, Rs σ = if σ.2.1 ∈ G.Uminus U sp then Rm σ else Rp σ := fun _ => rfl
  have hside : ∀ σ ∈ G.allSub Dm I, (σ.2.1 ∈ G.Uminus U sp ∧ σ ∈ G.PiMinus U Dm sp I) ∨
      (σ.2.1 ∉ G.Uminus U sp ∧ σ ∈ G.PiPlus U Dm sp I) := by
    intro σ hσ
    by_cases h : σ.2.1 ∈ G.Uminus U sp
    · left
      refine ⟨h, ?_⟩
      simp only [PiMinus, subMinus, Multiset.mem_toFinset, Multiset.mem_filter]
      exact ⟨hσ, h⟩
    · right
      refine ⟨h, ?_⟩
      simp only [PiPlus, subPlus, Multiset.mem_toFinset, Multiset.mem_filter]
      rcases hV.2.1 σ hσ with h' | h'
      · exact absurd h'.1 h
      · exact ⟨hσ, h'.1⟩
  have hpath : ∀ σ ∈ G.allSub Dm I, G.IsDemandPath U σ (Rs σ) := by
    intro σ hσ
    rcases hside σ hσ with ⟨h, h'⟩ | ⟨h, h'⟩
    · obtain ⟨a1, a2, a3, a4, a5⟩ := hRm σ h'
      rw [hRs]; simp only [h, ↓reduceIte]
      exact ⟨a1, a2, a3, fun v hv => (Finset.mem_filter.1 (a4 v hv)).1, a5⟩
    · obtain ⟨a1, a2, a3, a4, a5⟩ := hRp σ h'
      rw [hRs]; simp only [h, ↓reduceIte]
      exact ⟨a1, a2, a3, fun v hv => (Finset.mem_filter.1 (a4 v hv)).1, a5⟩
  have hdisj : ∀ σ ∈ G.allSub Dm I, ∀ σ' ∈ G.allSub Dm I, σ ≠ σ' →
      ∀ v ∈ Rs σ, v ∉ Rs σ' := by
    intro σ hσ σ' hσ' hne v hv hv'
    rcases hside σ hσ with ⟨h, h1⟩ | ⟨h, h1⟩ <;>
      rcases hside σ' hσ' with ⟨h', h1'⟩ | ⟨h', h1'⟩
    · rw [hRs] at hv hv'; simp only [h, h', ↓reduceIte] at hv hv'
      exact hRmd σ h1 σ' h1' hne v hv hv'
    · rw [hRs] at hv hv'; simp only [h, h', ↓reduceIte] at hv hv'
      exact G.uminus_uplus_disj hsp ((hRm σ h1).2.2.2.1 v hv) ((hRp σ' h1').2.2.2.1 v hv')
    · rw [hRs] at hv hv'; simp only [h, h', ↓reduceIte] at hv hv'
      exact G.uminus_uplus_disj hsp ((hRm σ' h1').2.2.2.1 v hv') ((hRp σ h1).2.2.2.1 v hv)
    · rw [hRs] at hv hv'; simp only [h, h', ↓reduceIte] at hv hv'
      exact hRpd σ h1 σ' h1' hne v hv hv'
  have hmemSub : ∀ δ ∈ Dm, ∀ σ ∈ G.chain I δ, σ ∈ G.allSub Dm I := by
    intro δ hδ σ hσ
    rw [allSub, Multiset.mem_bind]
    exact ⟨δ, hδ, Multiset.mem_coe.2 hσ⟩
  obtain ⟨hcnd, hcdisj⟩ := G.chain_nodup_disj (nodup_of_nodup_bind_demandEnds hV.2.2.1)
  refine ⟨fun δ => ((G.chain I δ).map Rs).flatten, ?_, ?_⟩
  · intro δ hδ
    have hfl := flatten_chainL (G.inD δ.1) δ.1 Rs δ.2.1 (G.sortedArcs I δ) δ.2.2
      (fun σ hσ => by
        have hl : σ.1 = δ.1 := label_of_mem_chainL hσ
        rw [← G.chain_eq_chainL I δ] at hσ
        obtain ⟨a1, a2, -, -, a5⟩ := hpath σ (hmemSub δ hδ σ hσ)
        refine ⟨a1, a2, ?_⟩
        rw [← hl]; exact a5)
      (fun e he => G.inD_of_mem_sortedArcs hI he)
    rw [← G.chain_eq_chainL I δ] at hfl
    obtain ⟨b1, b2, b3⟩ := hfl
    refine ⟨b1, b2, ?_, ?_, b3⟩
    · rw [List.nodup_flatten]
      refine ⟨fun r hr => ?_, ?_⟩
      · obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 hr
        exact (hpath σ (hmemSub δ hδ σ hσ)).2.2.1
      · rw [List.pairwise_map]
        refine List.Pairwise.imp_of_mem ?_ (hcnd δ hδ)
        intro σ σ' hσ hσ' hne v hv hv'
        exact hdisj σ (hmemSub δ hδ σ hσ) σ' (hmemSub δ hδ σ' hσ') hne v hv hv'
    · intro v hv
      obtain ⟨r, hr, hvr⟩ := List.mem_flatten.1 hv
      obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 hr
      exact (hpath σ (hmemSub δ hδ σ hσ)).2.2.2.1 v hvr
  · intro δ hδ δ' hδ' hne v hv hv'
    obtain ⟨r, hr, hvr⟩ := List.mem_flatten.1 hv
    obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 hr
    obtain ⟨r', hr', hvr'⟩ := List.mem_flatten.1 hv'
    obtain ⟨σ', hσ', rfl⟩ := List.mem_map.1 hr'
    have hne' : σ ≠ σ' := by
      rintro rfl; exact hcdisj δ hδ δ' hδ' hne σ hσ hσ'
    exact hdisj σ (hmemSub δ hδ σ hσ) σ' (hmemSub δ' hδ' σ' hσ') hne' v hvr hvr'

/-- lem:sound, by strong induction on `|U|`. -/
theorem sound_aux : ∀ (n : ℕ) (U : Finset V) (Dm : Finset (Demand V k)), U.card = n →
    (∀ δ ∈ Dm, δ.2.1 ∈ U ∧ δ.2.2 ∈ U) → G.Tab U Dm → G.Sem U Dm := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro U Dm hn hends h
    rw [Tab_eq] at h
    split_ifs at h with hpc
    · exact (G.lem_pebbling U hpc Dm hends).1 h.2
    · obtain ⟨sp, hsp, I, hI, hV, hm, hp⟩ := h
      exact G.sound_split hsp hI hV
        (ih _ (by rw [← hn]; exact G.card_Uminus_lt hsp) _ _ rfl (G.ends_PiMinus hsp hV) hm)
        (ih _ (by rw [← hn]; exact G.card_Uplus_lt hsp) _ _ rfl (G.ends_PiPlus hsp hV) hp)

end Instance

end DSPP
