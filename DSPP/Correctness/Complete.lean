/-
Completeness of the table (lem:complete): helper lemmas.

Paper: "Directed k Disjoint Shortest Paths Is Polynomial for Every Fixed k" (Saeed Amiri),
Section "The algorithm", subsection "Correctness".

For a solution `P_1, ..., P_k` and a vertex set `W`, `Π(W)` is the set of demands
`(l, first, last)` of the pieces of the paths `P_l` in `W`.  By induction over the hierarchy of
thm:hierarchy, `T(V(C), Π(V(C)))` holds at every cell `C` with `V(C) ≠ ∅`.
-/
import DSPP.Correctness.Lists
import DSPP.HierarchyThm

open Classical

namespace DSPP

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
theorem headD_mem {r : List V} (h : r ≠ []) (d : V) : r.headD d ∈ r := by
  obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil h
  simp

omit [DecidableEq V] in
theorem getLastD_mem {r : List V} (h : r ≠ []) (d : V) : r.getLastD d ∈ r := by
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast h]
  exact List.getLast_mem h

omit [DecidableEq V] in
theorem head?_eq_headD {r : List V} (h : r ≠ []) (d : V) : r.head? = some (r.headD d) := by
  obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil h
  simp

omit [DecidableEq V] in
theorem getLast?_eq_getLastD {r : List V} (h : r ≠ []) (d : V) :
    r.getLast? = some (r.getLastD d) := by
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast h]
  rfl

/-- The sum of a family of multisets, bound by `g`. -/
theorem sum_bind {ι α β : Type*} (s : Finset ι) (m : ι → Multiset α) (g : α → Multiset β) :
    (∑ i ∈ s, m i).bind g = ∑ i ∈ s, (m i).bind g := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Multiset.add_bind, ih]

/-- A list strictly sorted by a key has no two elements with the same key. -/
theorem inj_of_pairwise_lt {α : Type*} {f : α → ℝ} {X : List α}
    (hX : X.Pairwise (fun a b => f a < f b)) :
    ∀ a ∈ X, ∀ b ∈ X, f a = f b → a = b := by
  intro a ha b hb hab
  by_contra hne
  have h1 : X.Pairwise (fun a b => f a ≠ f b) := hX.imp (fun h => ne_of_lt h)
  have : ∀ a b, f a ≠ f b → f b ≠ f a := fun a b h => Ne.symm h
  have : Std.Symm (fun a b => f a ≠ f b) := ⟨this⟩
  exact h1.forall ha hb hne hab

/-- Two lists that are strictly sorted by a real key and are permutations of each other are
equal. -/
theorem eq_of_perm_of_pairwise_lt {α : Type*} (f : α → ℝ) :
    ∀ (l₁ l₂ : List α), l₁.Perm l₂ → l₁.Pairwise (fun a b => f a < f b) →
      l₂.Pairwise (fun a b => f a < f b) → l₁ = l₂
  | [], _, hp, _, _ => (List.nil_perm.1 hp).symm
  | a :: l₁, [], hp, _, _ => absurd (List.perm_nil.1 hp) (by simp)
  | a :: l₁, b :: l₂, hp, h₁, h₂ => by
    have ha : a ∈ b :: l₂ := hp.subset (by simp)
    have hb : b ∈ a :: l₁ := hp.symm.subset (by simp)
    rw [List.pairwise_cons] at h₁ h₂
    have hab : a = b := by
      rcases List.mem_cons.1 ha with h | h
      · exact h
      · rcases List.mem_cons.1 hb with h' | h'
        · exact h'.symm
        · exact absurd ((h₁.1 b h').trans (h₂.1 a h)) (lt_irrefl _)
    subst hab
    rw [eq_of_perm_of_pairwise_lt f l₁ l₂ ((List.perm_cons a).1 hp) h₁.2 h₂.2]

/-- A list that is strictly sorted by a real key is the merge sort of its set of elements. -/
theorem mergeSort_toFinset_eq {α : Type*} [DecidableEq α] (f : α → ℝ) (X : List α)
    (hX : X.Pairwise (fun a b => f a < f b)) :
    X.toFinset.toList.mergeSort (fun a b => decide (f a ≤ f b)) = X := by
  have hnd : X.Nodup := hX.imp (fun h e => by subst e; exact lt_irrefl _ h)
  have hinj := inj_of_pairwise_lt hX
  have hp : (X.toFinset.toList.mergeSort (fun a b => decide (f a ≤ f b))).Perm X :=
    (List.mergeSort_perm _ _).trans (List.toFinset_toList hnd)
  have hs := List.pairwise_mergeSort (le := fun a b => decide (f a ≤ f b))
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; exact hab.trans hbc)
    (fun a b => by simpa using le_total (f a) (f b)) X.toFinset.toList
  simp only [decide_eq_true_eq] at hs
  have hnd' := hp.nodup_iff.2 hnd
  have hs' : (X.toFinset.toList.mergeSort (fun a b => decide (f a ≤ f b))).Pairwise
      (fun a b => f a < f b) := by
    refine (hs.and hnd').imp_of_mem ?_
    intro a b ha hb ⟨h1, h2⟩
    exact lt_of_le_of_ne h1 (fun h => h2 (hinj a (hp.subset ha) b (hp.subset hb) h))
  exact eq_of_perm_of_pairwise_lt f _ _ hp hs' hX

variable {k : ℕ} [NeZero k] [Fintype V]

namespace Instance

variable (G : Instance V k)

/-! ### Cells and their children -/

theorem mem_cellVerts_lower {C : Cell k} {j : StarIdx k} {lam : ℝ} (hlo : C.lo j < lam)
    (hhi : lam < C.hi j) (v : V) :
    v ∈ G.cellVerts (C.lower j lam) ↔ v ∈ G.cellVerts C ∧ G.starX j v ≤ lam := by
  have hmax : max (C.lo j) lam = lam := max_eq_right hlo.le
  simp only [cellVerts, Finset.mem_filter, Finset.mem_univ, true_and, Cell.carrier,
    Set.mem_setOf_eq, Cell.lower, starX, Xv]
  constructor
  · intro h
    have hj := h j
    rw [Function.update_self, hmax] at hj
    refine ⟨fun j' => ?_, hj.2⟩
    by_cases hj' : j' = j
    · subst hj'; exact ⟨hj.1, hj.2.trans hhi.le⟩
    · have := h j'; rwa [Function.update_of_ne hj'] at this
  · rintro ⟨h, hl⟩ j'
    by_cases hj' : j' = j
    · subst hj'; rw [Function.update_self, hmax]; exact ⟨(h j').1, hl⟩
    · rw [Function.update_of_ne hj']; exact h j'

theorem mem_cellVerts_upper {C : Cell k} {j : StarIdx k} {lam : ℝ} (hlo : C.lo j < lam)
    (hhi : lam < C.hi j) (v : V) :
    v ∈ G.cellVerts (C.upper j lam) ↔ v ∈ G.cellVerts C ∧ lam ≤ G.starX j v := by
  have hmin : min (C.hi j) lam = lam := min_eq_right hhi.le
  simp only [cellVerts, Finset.mem_filter, Finset.mem_univ, true_and, Cell.carrier,
    Set.mem_setOf_eq, Cell.upper, starX, Xv]
  constructor
  · intro h
    have hj := h j
    rw [Function.update_self, hmin] at hj
    refine ⟨fun j' => ?_, hj.1⟩
    by_cases hj' : j' = j
    · subst hj'; exact ⟨hlo.le.trans hj.1, hj.2⟩
    · have := h j'; rwa [Function.update_of_ne hj'] at this
  · rintro ⟨h, hl⟩ j'
    by_cases hj' : j' = j
    · subst hj'; rw [Function.update_self, hmin]; exact ⟨hl, (h j').2⟩
    · rw [Function.update_of_ne hj']; exact h j'

omit [NeZero k] in
theorem atMostOneClass_of_isPointClass {U : Finset V} (h : G.IsPointClass U) :
    G.AtMostOneClass U := by
  obtain ⟨v, rfl⟩ := h
  intro a ha b hb i j
  simp only [pointClass, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  exact (ha i j).symm.trans (hb i j)

section Solution

variable (Ps : Fin k → List V)

/-- The multiset of the demands of the pieces of `P_1, ..., P_k` in `W`. -/
noncomputable def PiM (W : Finset V) : Multiset (Demand V k) :=
  ∑ l, (((pieces W (Ps l)).map (dem l (G.s 0))) : Multiset (Demand V k))

/-- `Π(W)`: the demands of the pieces of `P_1, ..., P_k` in `W`. -/
noncomputable def PiOf (W : Finset V) : Finset (Demand V k) := (G.PiM Ps W).toFinset

theorem mem_PiM {W : Finset V} {σ : Demand V k} :
    σ ∈ G.PiM Ps W ↔ ∃ l, ∃ r ∈ pieces W (Ps l), σ = dem l (G.s 0) r := by
  simp only [PiM, Multiset.mem_sum, Finset.mem_univ, true_and, Multiset.mem_coe,
    List.mem_map]
  constructor
  · rintro ⟨l, r, hr, rfl⟩; exact ⟨l, r, hr, rfl⟩
  · rintro ⟨l, r, hr, rfl⟩; exact ⟨l, r, hr, rfl⟩

theorem card_PiM (W : Finset V) : Multiset.card (G.PiM Ps W) = numPieces Ps W := by
  simp [PiM, numPieces, Multiset.card_sum]

theorem ends_PiM {W : Finset V} {σ : Demand V k} (h : σ ∈ G.PiM Ps W) :
    σ.2.1 ∈ W ∧ σ.2.2 ∈ W := by
  obtain ⟨l, r, hr, rfl⟩ := (G.mem_PiM Ps).1 h
  obtain ⟨hne, hW, -⟩ := mem_pieces hr
  exact ⟨hW _ (headD_mem hne _), hW _ (getLastD_mem hne _)⟩

omit [NeZero k] [Fintype V] in
/-- `demandEnds` of the demand of a non-empty list is a sub-multiset of the list. -/
theorem demandEnds_dem_le (l : Fin k) (d : V) {r : List V} (hr : r ≠ []) :
    demandEnds (dem l d r) ≤ (r : Multiset V) := by
  have hnd : (demandEnds (dem l d r)).Nodup := by
    unfold demandEnds; split_ifs with h
    · simp
    · simpa using h
  rw [Multiset.le_iff_subset hnd]
  intro v hv
  unfold demandEnds at hv
  split_ifs at hv
  · simp only [Multiset.mem_singleton] at hv; subst hv; exact headD_mem hr d
  · simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact headD_mem hr d
    · exact getLastD_mem hr d

omit [NeZero k] [Fintype V] in
theorem bind_demandEnds_le (l : Fin k) (d : V) (W : Finset V) (R : List V) :
    (((pieces W R).map (dem l d) : List (Demand V k)) : Multiset (Demand V k)).bind demandEnds ≤
      ((R.filter (· ∈ W) : List V) : Multiset V) := by
  rw [← flatten_pieces]
  have : ∀ L : List (List V), (∀ r ∈ L, r ≠ []) →
      ((L.map (dem l d) : List (Demand V k)) : Multiset (Demand V k)).bind demandEnds ≤
        ((L.flatten : List V) : Multiset V) := by
    intro L hL
    induction L with
    | nil => simp
    | cons r L ih =>
      simp only [List.map_cons, List.flatten_cons, ← Multiset.cons_coe, Multiset.cons_bind,
        ← Multiset.coe_add]
      exact add_le_add (demandEnds_dem_le l d (hL r (by simp)))
        (ih (fun r' hr' => hL r' (List.mem_cons_of_mem _ hr')))
  exact this _ (fun r hr => (mem_pieces hr).1)

variable {G Ps}

omit [NeZero k] in
/-- The vertices of a solution, as one multiset, have no repetitions. -/
theorem nodup_sum_paths (hP : G.IsSolution Ps) : (∑ l, (Ps l : Multiset V)).Nodup := by
  have : ∀ s : Finset (Fin k), (∑ l ∈ s, (Ps l : Multiset V)).Nodup := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Multiset.nodup_add]
      refine ⟨Multiset.coe_nodup.2 (hP.1 a).1.2, ih, ?_⟩
      rw [Multiset.disjoint_left]
      intro v hv hv'
      obtain ⟨l, hl, hv''⟩ := Multiset.mem_sum.1 hv'
      exact hP.2 a l (fun h => ha (h ▸ hl)) v hv hv''
  exact this _

/-- (V2) for the pieces of a solution in two disjoint sets. -/
theorem nodup_ends (hP : G.IsSolution Ps) {A B : Finset V} (hAB : ∀ v, v ∈ A → v ∉ B) :
    ((G.PiM Ps A + G.PiM Ps B).bind demandEnds).Nodup := by
  refine Multiset.nodup_of_le ?_ (nodup_sum_paths hP)
  rw [Multiset.add_bind, PiM, PiM, sum_bind, sum_bind, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun l _ => ?_)
  refine (add_le_add (bind_demandEnds_le l _ A (Ps l)) (bind_demandEnds_le l _ B (Ps l))).trans ?_
  rw [← Multiset.filter_coe, ← Multiset.filter_coe]
  calc Multiset.filter (· ∈ A) (Ps l : Multiset V) + Multiset.filter (· ∈ B) (Ps l : Multiset V)
      ≤ Multiset.filter (· ∈ A) (Ps l : Multiset V) +
          Multiset.filter (fun v => ¬ v ∈ A) (Ps l : Multiset V) :=
        add_le_add le_rfl (Multiset.monotone_filter_right _ (fun v hv hvA => hAB v hvA hv))
    _ = (Ps l : Multiset V) := Multiset.filter_add_not _ _

theorem nodup_PiM (hP : G.IsSolution Ps) (W : Finset V) : (G.PiM Ps W).Nodup := by
  have h := nodup_ends hP (A := W) (B := ∅) (by simp)
  have h0 : G.PiM Ps ∅ = 0 := by
    simp only [PiM]
    refine Finset.sum_eq_zero (fun l _ => ?_)
    have : pieces (∅ : Finset V) (Ps l) = [] := by
      cases hp : pieces (∅ : Finset V) (Ps l) with
      | nil => rfl
      | cons r rest =>
        obtain ⟨hne, hU, -⟩ := mem_pieces (hp ▸ List.mem_cons_self : r ∈ pieces ∅ (Ps l))
        obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil r hne
        exact absurd (hU v hv) (by simp)
    simp [this]
  rw [h0, add_zero] at h
  exact nodup_of_nodup_bind_demandEnds h

theorem PiOf_val (hP : G.IsSolution Ps) (W : Finset V) : (G.PiOf Ps W).val = G.PiM Ps W := by
  rw [PiOf, Multiset.toFinset_val, Multiset.dedup_eq_self.2 (nodup_PiM hP W)]

theorem mem_PiOf (_hP : G.IsSolution Ps) {W : Finset V} {σ : Demand V k} :
    σ ∈ G.PiOf Ps W ↔ ∃ l, ∃ r ∈ pieces W (Ps l), σ = dem l (G.s 0) r := by
  rw [PiOf, Multiset.mem_toFinset, G.mem_PiM Ps]

omit [NeZero k] in
/-- The paths of a solution are `D_l`-paths. -/
theorem isDPath_of_solution (hP : G.IsSolution Ps) (l : Fin k) : G.IsDPath l (Ps l) := by
  have h := hP.1 l
  refine ⟨?_, (G.lem_Di_b h.1).1 h, h.1.2⟩
  intro h0; have := h.1.1.1; rw [h0] at this; simp at this

omit [NeZero k] in
/-- A piece of `P_l` is a `D_l`-path inside `W`. -/
theorem piece_props (hP : G.IsSolution Ps) {W : Finset V} {l : Fin k} {r : List V}
    (hr : r ∈ pieces W (Ps l)) :
    r ≠ [] ∧ (∀ v ∈ r, v ∈ W) ∧ r.Nodup ∧ r.IsChain (G.inD l) ∧ (∀ v ∈ r, v ∈ Ps l) := by
  obtain ⟨hne, hW, hinf⟩ := mem_pieces hr
  have hD := isDPath_of_solution hP l
  exact ⟨hne, hW, List.Nodup.sublist hinf.sublist hD.2.2, hD.2.1.infix hinf,
    fun v hv => hinf.subset hv⟩

/-- Pieces of a solution with the same demand label and first vertex coincide. -/
theorem piece_eq_of_dem (hP : G.IsSolution Ps) {W : Finset V} {l l' : Fin k} {r r' : List V}
    (hr : r ∈ pieces W (Ps l)) (hr' : r' ∈ pieces W (Ps l'))
    (h : dem l (G.s 0) r = dem l' (G.s 0) r') : l = l' ∧ r = r' := by
  simp only [dem, Prod.mk.injEq] at h
  obtain ⟨rfl, hh, -⟩ := h
  refine ⟨rfl, ?_⟩
  by_contra hne
  have h1 := (piece_props hP hr).1
  have h1' := (piece_props hP hr').1
  exact pieces_disjoint (hP.1 l).1.2 hr hr' hne _ (headD_mem h1 _) (hh ▸ headD_mem h1' _)

/-- The pieces of a solution witness `S(W, Π(W))`. -/
theorem sem_PiOf (hP : G.IsSolution Ps) (W : Finset V) : G.Sem W (G.PiOf Ps W) := by
  let Rw : Demand V k → List V := fun δ =>
    if h : ∃ r ∈ pieces W (Ps δ.1), dem δ.1 (G.s 0) r = δ then Classical.choose h else []
  have hRw : ∀ δ ∈ G.PiOf Ps W, Rw δ ∈ pieces W (Ps δ.1) ∧ dem δ.1 (G.s 0) (Rw δ) = δ := by
    intro δ hδ
    obtain ⟨l, r, hr, rfl⟩ := (mem_PiOf hP).1 hδ
    have h : ∃ r' ∈ pieces W (Ps (dem l (G.s 0) r).1), dem (dem l (G.s 0) r).1 (G.s 0) r' =
        dem l (G.s 0) r := ⟨r, hr, rfl⟩
    simp only [Rw, h, ↓reduceDIte]
    exact Classical.choose_spec h
  refine ⟨Rw, ?_, ?_⟩
  · intro δ hδ
    obtain ⟨h1, h2⟩ := hRw δ hδ
    obtain ⟨hne, hW, hnd, hch, -⟩ := piece_props hP h1
    refine ⟨?_, ?_, hnd, hW, hch⟩
    · rw [head?_eq_headD hne (G.s 0)]
      exact congrArg (fun σ : Demand V k => some σ.2.1) h2
    · rw [getLast?_eq_getLastD hne (G.s 0)]
      exact congrArg (fun σ : Demand V k => some σ.2.2) h2
  · intro δ hδ δ' hδ' hne v hv hv'
    obtain ⟨h1, h2⟩ := hRw δ hδ
    obtain ⟨h1', h2'⟩ := hRw δ' hδ'
    by_cases hl : δ.1 = δ'.1
    · have hr : Rw δ ≠ Rw δ' := by
        intro h; apply hne; rw [← h2, ← h2', h, hl]
      rw [← hl] at h1'
      exact pieces_disjoint (hP.1 δ.1).1.2 h1 h1' hr v hv hv'
    · exact hP.2 δ.1 δ'.1 hl v ((piece_props hP h1).2.2.2.2 v hv)
        ((piece_props hP h1').2.2.2.2 v hv')

/-- At the root, every path is one piece: `Π(V) = Π_0`. -/
theorem PiOf_univ (hP : G.IsSolution Ps) : G.PiOf Ps Finset.univ = G.Pi0 := by
  ext σ
  rw [mem_PiOf hP, Pi0, Finset.mem_image]
  have hpc : ∀ l, pieces Finset.univ (Ps l) = [Ps l] := fun l =>
    pieces_of_subset (isDPath_of_solution hP l).1 (by simp)
  have hdem : ∀ l, dem l (G.s 0) (Ps l) = (l, G.s l, G.t l) := by
    intro l
    have hne := (isDPath_of_solution hP l).1
    have h1 := (hP.1 l).1.1.1
    have h2 := (hP.1 l).1.1.2.1
    rw [head?_eq_headD hne (G.s 0), Option.some.injEq] at h1
    rw [getLast?_eq_getLastD hne (G.s 0), Option.some.injEq] at h2
    simp only [dem, h1, h2]
  constructor
  · rintro ⟨l, r, hr, rfl⟩
    rw [hpc, List.mem_singleton] at hr
    subst hr
    exact ⟨l, Finset.mem_univ _, (hdem l).symm⟩
  · rintro ⟨l, -, rfl⟩
    exact ⟨l, Ps l, by rw [hpc]; simp, (hdem l).symm⟩

/-! ### Leaves -/

/-- Leaves: at a point class the leaf rule holds for `Π(U)`. -/
theorem tab_leaf (hP : G.IsSolution Ps) {U : Finset V} (hbox : G.IsBoxSet U)
    (hone : G.AtMostOneClass U) : G.Tab U (G.PiOf Ps U) := by
  have hpc := (G.lem_box_e hbox).2 hone
  rw [Tab_eq]
  simp only [hpc, ↓reduceIte]
  refine ⟨?_, (G.lem_pebbling U hpc _ (fun δ hδ => G.ends_PiM Ps
    (by rwa [PiOf, Multiset.mem_toFinset] at hδ))).2 (sem_PiOf hP U)⟩
  -- every path has at most one piece in a point class (lem:classpiece)
  have hlen : ∀ l, (pieces U (Ps l)).length ≤ 1 := by
    intro l
    by_contra h
    obtain ⟨i, j, m, hij, hjm, hm, hi, hj, hm'⟩ :=
      exists_gap_of_two_pieces (U := U) (Nat.lt_of_not_le h)
    obtain ⟨v, hv⟩ := hpc
    rw [hv] at hi hj hm'
    simp only [pointClass, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj hm'
    have hcl := G.lem_classpiece (isDPath_of_solution hP l) hij.le hjm.le hm
      (fun a b => (hi a b).symm.trans (hm' a b))
    exact hj (fun a b => (hi a b).trans (hcl a b))
  intro δ hδ δ' hδ' hl
  obtain ⟨l, r, hr, rfl⟩ := (mem_PiOf hP).1 hδ
  obtain ⟨l', r', hr', rfl⟩ := (mem_PiOf hP).1 hδ'
  obtain rfl : l = l' := by simpa [dem] using hl
  have hl1 := hlen l
  cases hpl : pieces U (Ps l) with
  | nil => rw [hpl] at hr; simp at hr
  | cons a rest =>
    rw [hpl] at hl1 hr hr'
    have hrest : rest = [] := by simpa using hl1
    subst hrest
    rw [List.mem_singleton] at hr hr'
    rw [hr, hr']

/-! ### Cuts -/

/-- Cuts: if both children of a cut have vertices, the split rule holds at `V(C)` with the
split at the cut and the interface of the crossing arcs, given the entries of the children. -/
theorem tab_cut (hP : G.IsSolution Ps) {C : Cell k} {j : StarIdx k} {lam : ℝ}
    (hg : G.IsGeneric j lam) (hlo : C.lo j < lam) (hhi : lam < C.hi j)
    (hnot : ¬ G.AtMostOneClass (G.cellVerts C))
    (hcross : G.crossArcCount Ps C j lam ≤ 3 * k - 4)
    (hpm : numPieces Ps (G.cellVerts (C.lower j lam)) ≤ P k)
    (hpp : numPieces Ps (G.cellVerts (C.upper j lam)) ≤ P k)
    (hm : (G.cellVerts (C.lower j lam)).Nonempty) (hp : (G.cellVerts (C.upper j lam)).Nonempty)
    (ihm : G.Tab (G.cellVerts (C.lower j lam)) (G.PiOf Ps (G.cellVerts (C.lower j lam))))
    (ihp : G.Tab (G.cellVerts (C.upper j lam)) (G.PiOf Ps (G.cellVerts (C.upper j lam)))) :
    G.Tab (G.cellVerts C) (G.PiOf Ps (G.cellVerts C)) := by
  set U := G.cellVerts C with hUdef
  set Um := G.cellVerts (C.lower j lam) with hUmdef
  set Up := G.cellVerts (C.upper j lam) with hUpdef
  have hmem_m : ∀ v, v ∈ Um ↔ v ∈ U ∧ G.starX j v ≤ lam := G.mem_cellVerts_lower hlo hhi
  have hmem_p : ∀ v, v ∈ Up ↔ v ∈ U ∧ lam ≤ G.starX j v := G.mem_cellVerts_upper hlo hhi
  have hd : ∀ v, v ∈ Um → v ∉ Up := by
    intro v h1 h2
    exact hg v (le_antisymm ((hmem_m v).1 h1).2 ((hmem_p v).1 h2).2)
  have hU : ∀ v ∈ U, v ∈ Um ∨ v ∈ Up := by
    intro v hv
    rcases le_total (G.starX j v) lam with h | h
    · exact Or.inl ((hmem_m v).2 ⟨hv, h⟩)
    · exact Or.inr ((hmem_p v).2 ⟨hv, h⟩)
  have hUm : Um ⊆ U := fun v hv => ((hmem_m v).1 hv).1
  have hUp : Up ⊆ U := fun v hv => ((hmem_p v).1 hv).1
  -- the split
  set α := Um.sup' hm (G.starX j) with hα
  set α' := Up.inf' hp (G.starX j) with hα'
  have hαlt : α < lam := by
    rw [hα, Finset.sup'_lt_iff]
    intro v hv
    exact lt_of_le_of_ne ((hmem_m v).1 hv).2 (hg v)
  have hltα' : lam < α' := by
    rw [hα', Finset.lt_inf'_iff]
    intro v hv
    exact lt_of_le_of_ne ((hmem_p v).1 hv).2 (fun h => hg v h.symm)
  set sp : StarIdx k × ℝ × ℝ := (j, α, α') with hsp_def
  have hUminus : G.Uminus U sp = Um := by
    ext v
    simp only [Uminus, Finset.mem_filter, hsp_def]
    constructor
    · rintro ⟨hv, h⟩; exact (hmem_m v).2 ⟨hv, h.trans hαlt.le⟩
    · intro hv; exact ⟨hUm hv, Finset.le_sup' (G.starX j) hv⟩
  have hUplus : G.Uplus U sp = Up := by
    ext v
    simp only [Uplus, Finset.mem_filter, hsp_def]
    constructor
    · rintro ⟨hv, h⟩; exact (hmem_p v).2 ⟨hv, hltα'.le.trans h⟩
    · intro hv; exact ⟨hUp hv, Finset.inf'_le (G.starX j) hv⟩
  have hsp : sp ∈ G.splits U := by
    obtain ⟨a, ha, haα⟩ := Finset.exists_mem_eq_sup' hm (G.starX j)
    obtain ⟨b, hb, hbα⟩ := Finset.exists_mem_eq_inf' hp (G.starX j)
    refine Finset.mem_filter.2 ⟨?_, ?_⟩
    · refine Finset.mem_product.2 ⟨Finset.mem_univ _, Finset.mem_product.2 ⟨?_, ?_⟩⟩
      · exact Finset.mem_image.2 ⟨(j, a), Finset.mem_univ _, haα.symm⟩
      · exact Finset.mem_image.2 ⟨(j, b), Finset.mem_univ _, hbα.symm⟩
    · refine ⟨Finset.mem_image.2 ⟨a, hUm ha, haα.symm⟩,
        Finset.mem_image.2 ⟨b, hUp hb, hbα.symm⟩, hαlt.trans hltα', ?_⟩
      rintro v hv ⟨h1, h2⟩
      rcases hU v hv with h | h
      · exact absurd (Finset.le_sup' (G.starX j) h) (not_le.2 h1)
      · exact absurd (Finset.inf'_le (G.starX j) h) (not_le.2 h2)
  -- the interface of the crossing arcs
  set d := G.s 0 with hd_def
  set c : V × V → Bool := fun e => decide ((e.1 ∈ Um ∧ e.2 ∈ Up) ∨ (e.1 ∈ Up ∧ e.2 ∈ Um))
    with hc_def
  have hc : ∀ u v, (u ∈ Um ∨ u ∈ Up) → (v ∈ Um ∨ v ∈ Up) →
      (c (u, v) = true ↔ (u ∈ Um ∧ v ∈ Up ∨ u ∈ Up ∧ v ∈ Um)) := by
    intro u v _ _; simp [hc_def]
  have hcU : ∀ e, c e = true → e.1 ∈ U ∧ e.2 ∈ U := by
    intro e he
    simp only [hc_def, decide_eq_true_eq] at he
    rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨hUm h1, hUp h2⟩
    · exact ⟨hUp h1, hUm h2⟩
  set I : Finset (ArcDemand V k) := Finset.univ.biUnion fun l =>
    ((pieces U (Ps l)).flatMap fun r => ((arcs r).filter c).map fun e => (e, dem l d r)).toFinset
    with hI_def
  have hmemI : ∀ p, p ∈ I ↔
      ∃ l, ∃ r ∈ pieces U (Ps l), p.1 ∈ (arcs r).filter c ∧ p.2 = dem l d r := by
    intro p
    simp only [hI_def, Finset.mem_biUnion, Finset.mem_univ, true_and, List.mem_toFinset,
      List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨l, r, hr, e, he, rfl⟩; exact ⟨l, r, hr, he, rfl⟩
    · rintro ⟨l, r, hr, he, h2⟩; exact ⟨l, r, hr, p.1, he, by rw [← h2]⟩
  have hcard : I.card ≤ 3 * k - 4 := by
    refine (Finset.card_biUnion_le).trans ?_
    refine le_trans ?_ hcross
    refine (Finset.sum_le_sum fun l _ => List.toFinset_card_le _).trans (le_of_eq ?_)
    unfold crossArcCount
    refine Finset.sum_congr rfl fun l _ => ?_
    have := congrArg List.length (filter_arcs_pieces c hcU (Ps l))
    rw [this, List.length_flatMap, List.length_flatMap]
    simp only [List.length_map]
  have hI : I ∈ G.interfaces U (G.PiOf Ps U) sp := by
    simp only [interfaces, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨?_, hcard⟩
    intro p hpI
    obtain ⟨l, r, hr, he, h2⟩ := (hmemI p).1 hpI
    rw [List.mem_filter] at he
    simp only [candPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
    rw [hUminus, hUplus]
    refine ⟨(mem_PiOf hP).2 ⟨l, r, hr, h2⟩, ?_, ?_⟩
    · rw [h2]
      exact rel_of_mem_arcs_chain (piece_props hP hr).2.2.2.1 he.1
    · simpa [hc_def] using he.2
  have hassigned : ∀ l, ∀ r ∈ pieces U (Ps l),
      assigned I (dem l d r) = ((arcs r).filter c).toFinset := by
    intro l r hr
    ext e
    simp only [assigned, Finset.mem_image, Finset.mem_filter, List.mem_toFinset]
    constructor
    · rintro ⟨p, ⟨hpI, hp2⟩, rfl⟩
      obtain ⟨l', r', hr', he, h2⟩ := (hmemI p).1 hpI
      rw [hp2] at h2
      obtain ⟨rfl, rfl⟩ := piece_eq_of_dem hP hr hr' h2
      exact he
    · intro he
      exact ⟨(e, dem l d r), ⟨(hmemI _).2 ⟨l, r, hr, he, rfl⟩, rfl⟩, rfl⟩
  have hsorted : ∀ l, ∀ r ∈ pieces U (Ps l),
      ((arcs r).filter c).Pairwise (fun e e' => G.F l e.1 < G.F l e'.1) := by
    intro l r hr
    have hch := (piece_props hP hr).2.2.2.1
    have hlt : r.IsChain (fun u v => G.F l u < G.F l v) := hch.imp fun u v h => by
      have h1 := (G.lem_W0 h.1 l).2 h
      have h2 := G.len_pos u v h.1
      linarith
    have : Trans (fun u v => G.F l u < G.F l v) (fun u v => G.F l u < G.F l v)
        (fun u v => G.F l u < G.F l v) := ⟨fun h1 h2 => lt_trans h1 h2⟩
    exact (arcs_pairwise (List.isChain_iff_pairwise.1 hlt)).filter _
  have hsortedArcs : ∀ l, ∀ r ∈ pieces U (Ps l),
      G.sortedArcs I (dem l d r) = (arcs r).filter c := by
    intro l r hr
    unfold sortedArcs
    rw [hassigned l r hr]
    exact mergeSort_toFinset_eq (fun e : V × V => G.F l e.1) _ (hsorted l r hr)
  have hchain : ∀ l, ∀ r ∈ pieces U (Ps l),
      (G.chain I (dem l d r) : Multiset (Demand V k)) =
        (((pieces Um r).map (dem l d) : List (Demand V k)) : Multiset (Demand V k)) +
          (((pieces Up r).map (dem l d) : List (Demand V k)) : Multiset (Demand V k)) := by
    intro l r hr
    have : G.chain I (dem l d r) = chainL l (r.headD d) ((arcs r).filter c) (r.getLastD d) := by
      rw [G.chain_eq_chainL, hsortedArcs l r hr]
      rfl
    rw [this]
    obtain ⟨hne, hW, -⟩ := piece_props hP hr
    exact chainL_pieces l d c hd hc hne (fun v hv => hU v (hW v hv))
  have hallSub : G.allSub (G.PiOf Ps U) I = G.PiM Ps Um + G.PiM Ps Up := by
    rw [allSub, PiOf_val hP, PiM, sum_bind, PiM, PiM, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← flatMap_pieces hUm (Ps l), ← flatMap_pieces hUp (Ps l)]
    have key : ∀ L : List (List V), (∀ r ∈ L, r ∈ pieces U (Ps l)) →
        (((L.map (dem l d) : List (Demand V k)) : Multiset (Demand V k))).bind
            (fun δ => (G.chain I δ : Multiset (Demand V k))) =
          (((L.flatMap (pieces Um)).map (dem l d) : List (Demand V k)) : Multiset _) +
            (((L.flatMap (pieces Up)).map (dem l d) : List (Demand V k)) : Multiset _) := by
      intro L hL
      induction L with
      | nil => simp
      | cons r L ih =>
        rw [List.map_cons, ← Multiset.cons_coe, Multiset.cons_bind,
          hchain l r (hL r (by simp)), ih (fun r' hr' => hL r' (List.mem_cons_of_mem _ hr')),
          List.flatMap_cons, List.flatMap_cons, List.map_append, List.map_append,
          ← Multiset.coe_add, ← Multiset.coe_add]
        exact add_add_add_comm _ _ _ _
    exact key _ fun r hr => hr
  have hsubMinus : G.subMinus U (G.PiOf Ps U) sp I = G.PiM Ps Um := by
    rw [subMinus, hallSub, hUminus, Multiset.filter_add]
    have h1 : Multiset.filter (fun σ : Demand V k => σ.2.1 ∈ Um) (G.PiM Ps Um) = G.PiM Ps Um :=
      Multiset.filter_eq_self.2 fun σ hσ => (G.ends_PiM Ps hσ).1
    have h2 : Multiset.filter (fun σ : Demand V k => σ.2.1 ∈ Um) (G.PiM Ps Up) = 0 :=
      Multiset.filter_eq_nil.2 fun σ hσ h => hd _ h (G.ends_PiM Ps hσ).1
    rw [h1, h2, add_zero]
  have hsubPlus : G.subPlus U (G.PiOf Ps U) sp I = G.PiM Ps Up := by
    rw [subPlus, hallSub, hUplus, Multiset.filter_add]
    have h1 : Multiset.filter (fun σ : Demand V k => σ.2.1 ∈ Up) (G.PiM Ps Up) = G.PiM Ps Up :=
      Multiset.filter_eq_self.2 fun σ hσ => (G.ends_PiM Ps hσ).1
    have h2 : Multiset.filter (fun σ : Demand V k => σ.2.1 ∈ Up) (G.PiM Ps Um) = 0 :=
      Multiset.filter_eq_nil.2 fun σ hσ h => hd _ (G.ends_PiM Ps hσ).1 h
    rw [h1, h2, zero_add]
  have hV : G.Valid U (G.PiOf Ps U) sp I := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro δ hδ
      obtain ⟨l, r, hr, rfl⟩ := (mem_PiOf hP).1 hδ
      intro e he e' he' hF
      rw [hassigned l r hr, List.mem_toFinset] at he he'
      exact inj_of_pairwise_lt (hsorted l r hr) e he e' he' hF
    · intro σ hσ
      rw [hallSub, Multiset.mem_add] at hσ
      rw [hUminus, hUplus]
      rcases hσ with h | h
      · exact Or.inl (G.ends_PiM Ps h)
      · exact Or.inr (G.ends_PiM Ps h)
    · rw [hallSub]; exact nodup_ends hP hd
    · rw [hsubMinus, card_PiM]; exact hpm
    · rw [hsubPlus, card_PiM]; exact hpp
  have hPiMinus : G.PiMinus U (G.PiOf Ps U) sp I = G.PiOf Ps Um := by
    rw [PiMinus, hsubMinus]; rfl
  have hPiPlus : G.PiPlus U (G.PiOf Ps U) sp I = G.PiOf Ps Up := by
    rw [PiPlus, hsubPlus]; rfl
  have hnpc : ¬ G.IsPointClass U := fun h => hnot (G.atMostOneClass_of_isPointClass h)
  rw [Tab_eq]
  simp only [hnpc, ↓reduceIte]
  refine ⟨sp, hsp, I, hI, hV, ?_, ?_⟩
  · rw [hPiMinus, hUminus]; exact ihm
  · rw [hPiPlus, hUplus]; exact ihp

/-! ### Induction over the hierarchy -/

/-- `T(V(C), Π(V(C)))` holds at every cell `C` of the hierarchy with `V(C) ≠ ∅`. -/
theorem tab_tree (hP : G.IsSolution Ps) (C0 : Cell k) (T0 : CutTree k)
    (hT0 : G.IsHierarchy T0 C0)
    (hH2 : ∀ C j lam, (C, some (j, lam)) ∈ T0.nodes C0 → G.crossNum Ps C j lam ≤ 3 * k - 4)
    (hH3 : ∀ C o, (C, o) ∈ T0.nodes C0 → numPieces Ps (G.cellVerts C) ≤ P k)
    (hH4 : ∀ C o, (C, o) ∈ T0.nodes C0 → (o = none ↔ G.AtMostOneClass (G.cellVerts C))) :
    ∀ (T : CutTree k) (C : Cell k), G.IsHierarchy T C → (∀ x ∈ T.nodes C, x ∈ T0.nodes C0) →
      (G.cellVerts C).Nonempty → G.Tab (G.cellVerts C) (G.PiOf Ps (G.cellVerts C)) := by
  have hroot : ∀ (T : CutTree k) (C' : Cell k), ∃ o, (C', o) ∈ T.nodes C' := by
    intro T C'; cases T <;> simp [CutTree.nodes]
  intro T
  induction T with
  | leaf =>
    intro C _ hsub hne
    have := (hH4 C none (hsub _ (by simp [CutTree.nodes]))).1 rfl
    exact tab_leaf hP (G.lem_box_c C hne) this
  | node j lam lt rt ihl ihr =>
    intro C hT hsub hne
    obtain ⟨hg, hlo, hhi, hl, hr⟩ := hT
    have hC : (C, some (j, lam)) ∈ T0.nodes C0 := hsub _ (by simp [CutTree.nodes])
    have hsubl : ∀ x ∈ lt.nodes (C.lower j lam), x ∈ T0.nodes C0 :=
      fun x hx => hsub x (by simp [CutTree.nodes, hx])
    have hsubr : ∀ x ∈ rt.nodes (C.upper j lam), x ∈ T0.nodes C0 :=
      fun x hx => hsub x (by simp [CutTree.nodes, hx])
    have hpm := hH3 _ _ (hsubl _ (hroot lt _).choose_spec)
    have hpp := hH3 _ _ (hsubr _ (hroot rt _).choose_spec)
    have hnot : ¬ G.AtMostOneClass (G.cellVerts C) := fun h => by
      have := (hH4 _ _ hC).2 h; simp at this
    have hcross := G.cor_crossarcs Ps C0 T0 hT0 hH2 C j lam hC
    have hmem_m := G.mem_cellVerts_lower (C := C) hlo hhi
    have hmem_p := G.mem_cellVerts_upper (C := C) hlo hhi
    by_cases hm : (G.cellVerts (C.lower j lam)).Nonempty
    · by_cases hp : (G.cellVerts (C.upper j lam)).Nonempty
      · exact tab_cut hP hg hlo hhi hnot hcross hpm hpp hm hp (ihl _ hl hsubl hm)
          (ihr _ hr hsubr hp)
      · have heq : G.cellVerts C = G.cellVerts (C.lower j lam) := by
          ext v
          rw [hmem_m]
          refine ⟨fun hv => ⟨hv, ?_⟩, fun h => h.1⟩
          by_contra h
          exact hp ⟨v, (hmem_p v).2 ⟨hv, (not_le.1 h).le⟩⟩
        rw [heq]; exact ihl _ hl hsubl hm
    · have heq : G.cellVerts C = G.cellVerts (C.upper j lam) := by
        ext v
        rw [hmem_p]
        refine ⟨fun hv => ⟨hv, ?_⟩, fun h => h.1⟩
        by_contra h
        exact hm ⟨v, (hmem_m v).2 ⟨hv, (not_le.1 h).le⟩⟩
      rw [heq] at hne ⊢; exact ihr _ hr hsubr hne

end Solution

/-- lem:complete, assembled: a solution gives `T(V, Π_0)`. -/
theorem complete_aux (h : G.HasSolution) : G.Tab Finset.univ G.Pi0 := by
  obtain ⟨Ps, hP⟩ := h
  obtain ⟨C0, T, hT, hH1, hH2, hH3, hH4⟩ := G.thm_hierarchy Ps (isDPath_of_solution hP)
  have hroot : G.cellVerts C0 = Finset.univ := by
    ext v; simp [cellVerts, hH1 v]
  have := tab_tree hP C0 T hT hH2 hH3 hH4 T C0 hT (fun x hx => hx)
    (by rw [hroot]; exact Finset.univ_nonempty_iff.2 ⟨G.s 0⟩)
  rwa [hroot, PiOf_univ hP] at this

end Instance

end DSPP
