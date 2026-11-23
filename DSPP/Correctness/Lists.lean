/-
List lemmas about pieces, arcs and chains, used for lem:complete.

Paper: "Directed k Disjoint Shortest Paths Is Polynomial for Every Fixed k" (Saeed Amiri),
Section "The algorithm", subsection "Correctness".
-/
import DSPP.Correctness.Sound

open Classical

namespace DSPP

variable {V : Type*} [DecidableEq V]

/-! ### Pieces: the cons equations -/

section Pieces

variable {U W : Finset V}

theorem pieces_nil : pieces U ([] : List V) = [] := by
  simp [pieces]

theorem pieces_cons_of_not_mem {x : V} (xs : List V) (hx : x ∉ U) :
    pieces U (x :: xs) = pieces U xs := by
  simp [pieces, List.splitOnP_cons_eq_ite_modifyHead, hx]

theorem pieces_singleton {x : V} (hx : x ∈ U) : pieces U [x] = [[x]] := by
  simp [pieces, List.splitOnP_cons_eq_ite_modifyHead, hx]

theorem pieces_cons_cons_of_not_mem {x y : V} (ys : List V) (hx : x ∈ U) (hy : y ∉ U) :
    pieces U (x :: y :: ys) = [x] :: pieces U (y :: ys) := by
  simp [pieces, List.splitOnP_cons_eq_ite_modifyHead, hx, hy]

theorem pieces_cons_cons_of_mem {x y : V} (ys : List V) (hx : x ∈ U) (hy : y ∈ U) :
    ∃ r rest, pieces U (y :: ys) = (y :: r) :: rest ∧
      pieces U (x :: y :: ys) = (x :: y :: r) :: rest := by
  obtain ⟨g, gs, hg⟩ : ∃ g gs, ys.splitOnP (fun v => !decide (v ∈ U)) = g :: gs := by
    cases h : ys.splitOnP (fun v => !decide (v ∈ U)) with
    | nil => exact absurd h (List.splitOnP_ne_nil _ _)
    | cons g gs => exact ⟨g, gs, rfl⟩
  refine ⟨g, gs.filter (fun p => !p.isEmpty), ?_, ?_⟩ <;>
    simp [pieces, List.splitOnP_cons_eq_ite_modifyHead, hx, hy, hg]

/-- The first piece of a list that starts in `U` starts with its first element and is a
prefix of the list. -/
theorem pieces_cons_of_mem {y : V} (ys : List V) (hy : y ∈ U) :
    ∃ r rest, pieces U (y :: ys) = (y :: r) :: rest ∧ (y :: r) <+: (y :: ys) := by
  induction ys generalizing y with
  | nil => exact ⟨[], [], pieces_singleton hy, List.prefix_refl _⟩
  | cons z zs ih =>
    by_cases hz : z ∈ U
    · obtain ⟨r, rest, h1, h2⟩ := pieces_cons_cons_of_mem zs hy hz
      obtain ⟨r', rest', h1', hp⟩ := ih hz
      rw [h1] at h1'
      simp only [List.cons.injEq, true_and] at h1'
      obtain ⟨rfl, rfl⟩ := h1'
      exact ⟨z :: r, rest, h2, List.prefix_cons_inj y |>.2 hp⟩
    · exact ⟨[], _, pieces_cons_cons_of_not_mem zs hy hz,
        List.prefix_cons_inj y |>.2 (List.nil_prefix)⟩

omit [DecidableEq V] in
/-- Induction principle for lists that looks at the first two elements. -/
theorem list_induction2 {p : List V → Prop} (h0 : p []) (h1 : ∀ x, p [x])
    (h2 : ∀ x y ys, p (y :: ys) → p (x :: y :: ys)) : ∀ R, p R
  | [] => h0
  | [x] => h1 x
  | x :: y :: ys => h2 x y ys (list_induction2 h0 h1 h2 (y :: ys))

/-- The pieces of `R`, concatenated, are the elements of `R` in `U`. -/
theorem flatten_pieces (R : List V) : (pieces U R).flatten = R.filter (· ∈ U) := by
  induction R using list_induction2 with
  | h0 => simp [pieces_nil]
  | h1 x =>
    by_cases hx : x ∈ U
    · simp [pieces_singleton hx, hx]
    · simp [pieces_cons_of_not_mem _ hx, pieces_nil, hx]
  | h2 x y ys ih =>
    by_cases hx : x ∈ U
    · by_cases hy : y ∈ U
      · obtain ⟨r, rest, h1, h2⟩ := pieces_cons_cons_of_mem ys hx hy
        rw [h1] at ih
        rw [h2, List.filter_cons_of_pos (by simpa using hx), ← ih]
        simp
      · rw [pieces_cons_cons_of_not_mem ys hx hy, List.filter_cons_of_pos (by simpa using hx),
          ← ih]
        simp
    · rw [pieces_cons_of_not_mem _ hx, List.filter_cons_of_neg (by simpa using hx), ih]

/-- Every piece is non-empty, lies in `U`, and is a contiguous part of `R`. -/
theorem mem_pieces {R r : List V} (h : r ∈ pieces U R) :
    r ≠ [] ∧ (∀ v ∈ r, v ∈ U) ∧ r <:+: R := by
  induction R using list_induction2 generalizing r with
  | h0 => simp [pieces_nil] at h
  | h1 x =>
    by_cases hx : x ∈ U
    · rw [pieces_singleton hx, List.mem_singleton] at h
      subst h
      exact ⟨by simp, by simpa using hx, List.infix_refl _⟩
    · simp [pieces_cons_of_not_mem _ hx, pieces_nil] at h
  | h2 x y ys ih =>
    by_cases hx : x ∈ U
    · by_cases hy : y ∈ U
      · obtain ⟨r', rest, h1, h2⟩ := pieces_cons_cons_of_mem ys hx hy
        rw [h2, List.mem_cons] at h
        rcases h with rfl | h
        · obtain ⟨-, hU, hinf⟩ := ih (r := y :: r') (by rw [h1]; simp)
          refine ⟨by simp, ?_, ?_⟩
          · intro v hv
            rcases List.mem_cons.1 hv with rfl | hv
            · exact hx
            · exact hU v hv
          · obtain ⟨r'', rest'', h1'', hpre⟩ := pieces_cons_of_mem (U := U) ys hy
            rw [h1] at h1''
            simp only [List.cons.injEq, true_and] at h1''
            obtain ⟨rfl, rfl⟩ := h1''
            exact (List.prefix_cons_inj x |>.2 hpre).isInfix
        · obtain ⟨hne, hU, hinf⟩ := ih (by rw [h1]; exact List.mem_cons_of_mem _ h)
          exact ⟨hne, hU, hinf.trans (List.suffix_cons _ _).isInfix⟩
      · rw [pieces_cons_cons_of_not_mem ys hx hy, List.mem_cons] at h
        rcases h with rfl | h
        · exact ⟨by simp, by simpa using hx, (List.prefix_cons_inj x |>.2
            (List.nil_prefix)).isInfix⟩
        · obtain ⟨hne, hU, hinf⟩ := ih h
          exact ⟨hne, hU, hinf.trans (List.suffix_cons _ _).isInfix⟩
    · rw [pieces_cons_of_not_mem _ hx] at h
      obtain ⟨hne, hU, hinf⟩ := ih h
      exact ⟨hne, hU, hinf.trans (List.suffix_cons _ _).isInfix⟩

/-- Pieces in a subset `W ⊆ U` are the pieces in `W` of the pieces in `U`. -/
theorem flatMap_pieces (hWU : W ⊆ U) (R : List V) :
    (pieces U R).flatMap (pieces W) = pieces W R := by
  induction R using list_induction2 with
  | h0 => simp [pieces_nil]
  | h1 x =>
    by_cases hx : x ∈ U
    · simp [pieces_singleton hx]
    · have hxW : x ∉ W := fun h => hx (hWU h)
      simp [pieces_cons_of_not_mem _ hx, pieces_cons_of_not_mem _ hxW, pieces_nil]
  | h2 x y ys ih =>
    by_cases hx : x ∈ U
    · by_cases hy : y ∈ U
      · obtain ⟨r, rest, h1, h2⟩ := pieces_cons_cons_of_mem ys hx hy
        rw [h1, List.flatMap_cons] at ih
        rw [h2, List.flatMap_cons]
        by_cases hxW : x ∈ W
        · by_cases hyW : y ∈ W
          · obtain ⟨r1, rest1, e1, e2⟩ := pieces_cons_cons_of_mem r hxW hyW
            obtain ⟨r2, rest2, f1, f2⟩ := pieces_cons_cons_of_mem ys hxW hyW
            rw [e1, f1] at ih
            rw [e2, f2]
            simp only [List.cons_append, List.cons.injEq, true_and] at ih ⊢
            exact ih
          · rw [pieces_cons_cons_of_not_mem r hxW hyW, pieces_cons_cons_of_not_mem ys hxW hyW,
              ← ih]
            simp
        · rw [pieces_cons_of_not_mem _ hxW, pieces_cons_of_not_mem _ hxW, ih]
      · have hyW : y ∉ W := fun h => hy (hWU h)
        rw [pieces_cons_cons_of_not_mem ys hx hy, List.flatMap_cons, ih]
        by_cases hxW : x ∈ W
        · rw [pieces_singleton hxW, pieces_cons_cons_of_not_mem ys hxW hyW]
          simp
        · rw [pieces_cons_of_not_mem _ hxW, pieces_cons_of_not_mem _ hxW, pieces_nil]
          simp
    · have hxW : x ∉ W := fun h => hx (hWU h)
      rw [pieces_cons_of_not_mem _ hx, pieces_cons_of_not_mem _ hxW, ih]

/-- A non-empty list inside `U` is its own only piece. -/
theorem pieces_of_subset {R : List V} (hR : R ≠ []) (hU : ∀ v ∈ R, v ∈ U) :
    pieces U R = [R] := by
  induction R using list_induction2 with
  | h0 => exact absurd rfl hR
  | h1 x => exact pieces_singleton (hU x (by simp))
  | h2 x y ys ih =>
    obtain ⟨r, rest, h1, h2⟩ := pieces_cons_cons_of_mem ys (hU x (by simp)) (hU y (by simp))
    have := ih (by simp) (fun v hv => hU v (List.mem_cons_of_mem _ hv))
    rw [h1] at this
    simp only [List.cons.injEq, true_and] at this
    obtain ⟨rfl, rfl⟩ := this
    exact h2

/-- Different pieces of a list without repetitions are disjoint. -/
theorem pieces_disjoint {R : List V} (hR : R.Nodup) {r r' : List V} (hr : r ∈ pieces U R)
    (hr' : r' ∈ pieces U R) (hne : r ≠ r') : ∀ v ∈ r, v ∉ r' := by
  have hnd : (pieces U R).flatten.Nodup := by
    rw [flatten_pieces]; exact hR.filter _
  rw [List.nodup_flatten] at hnd
  have := hnd.2.forall hr hr' hne
  intro v hv hv'
  exact this hv hv'

/-- Two pieces of `R` in `U` give positions `i < j < m` with `R[i], R[m] ∈ U` and
`R[j] ∉ U`. -/
theorem exists_gap_of_two_pieces {R : List V} (h : 2 ≤ (pieces U R).length) :
    ∃ i j m, ∃ _ : i < j, ∃ _ : j < m, ∃ hm : m < R.length,
      R[i]'(by omega) ∈ U ∧ R[j]'(by omega) ∉ U ∧ R[m] ∈ U := by
  induction R using list_induction2 with
  | h0 => simp [pieces_nil] at h
  | h1 x =>
    by_cases hx : x ∈ U
    · simp [pieces_singleton hx] at h
    · simp [pieces_cons_of_not_mem _ hx, pieces_nil] at h
  | h2 x y ys ih =>
    have shift : (∃ i j m, ∃ _ : i < j, ∃ _ : j < m, ∃ hm : m < (y :: ys).length,
        (y :: ys)[i]'(by omega) ∈ U ∧ (y :: ys)[j]'(by omega) ∉ U ∧ (y :: ys)[m] ∈ U) →
        ∃ i j m, ∃ _ : i < j, ∃ _ : j < m, ∃ hm : m < (x :: y :: ys).length,
          (x :: y :: ys)[i]'(by omega) ∈ U ∧ (x :: y :: ys)[j]'(by omega) ∉ U ∧
            (x :: y :: ys)[m] ∈ U := by
      rintro ⟨i, j, m, hij, hjm, hm, hi, hj, hm'⟩
      refine ⟨i + 1, j + 1, m + 1, by omega, by omega,
        by simp only [List.length_cons] at hm ⊢; omega, ?_, ?_, ?_⟩
      · simpa using hi
      · simpa using hj
      · simpa using hm'
    by_cases hx : x ∈ U
    · by_cases hy : y ∈ U
      · obtain ⟨r, rest, h1, h2⟩ := pieces_cons_cons_of_mem ys hx hy
        apply shift; apply ih
        rw [h1]; rw [h2] at h; simpa using h
      · rw [pieces_cons_cons_of_not_mem ys hx hy] at h
        obtain ⟨r, hr⟩ : ∃ r, r ∈ pieces U (y :: ys) := by
          cases hp : pieces U (y :: ys) with
          | nil => rw [hp] at h; simp at h
          | cons r rest => exact ⟨r, by simp⟩
        obtain ⟨hne, hrU, hinf⟩ := mem_pieces hr
        obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil r hne
        have hvU := hrU v hv
        have hv' : v ∈ y :: ys := hinf.subset hv
        have hvys : v ∈ ys := by
          rcases List.mem_cons.1 hv' with rfl | h'
          · exact absurd hvU hy
          · exact h'
        obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.1 hvys
        exact ⟨0, 1, m + 2, by omega, by omega, by simp; omega, by simpa using hx,
          by simpa using hy, by simpa using hvU⟩
    · rw [pieces_cons_of_not_mem _ hx] at h
      exact shift (ih h)

end Pieces

/-! ### Arcs -/

section Arcs

omit [DecidableEq V] in
theorem arcs_nil : arcs ([] : List V) = [] := rfl

omit [DecidableEq V] in
theorem arcs_singleton (x : V) : arcs [x] = [] := rfl

omit [DecidableEq V] in
theorem arcs_cons_cons_l (x y : V) (ys : List V) :
    arcs (x :: y :: ys) = (x, y) :: arcs (y :: ys) := rfl

omit [DecidableEq V] in
theorem mem_arcs {R : List V} {e : V × V} (h : e ∈ arcs R) : e.1 ∈ R ∧ e.2 ∈ R := by
  obtain ⟨h1, h2⟩ := List.of_mem_zip h
  exact ⟨h1, List.mem_of_mem_tail h2⟩

omit [DecidableEq V] in
theorem rel_of_mem_arcs_chain {rel : V → V → Prop} {R : List V} (hR : R.IsChain rel) {e : V × V}
    (h : e ∈ arcs R) : rel e.1 e.2 := by
  induction R using list_induction2 with
  | h0 => simp [arcs_nil] at h
  | h1 x => simp [arcs_singleton] at h
  | h2 x y ys ih =>
    rw [arcs_cons_cons_l, List.mem_cons] at h
    rw [List.isChain_cons_cons] at hR
    rcases h with rfl | h
    · exact hR.1
    · exact ih hR.2 h

omit [DecidableEq V] in
theorem arcs_pairwise {rel : V → V → Prop} {R : List V} (hR : R.Pairwise rel) :
    (arcs R).Pairwise (fun e e' => rel e.1 e'.1) := by
  induction R using list_induction2 with
  | h0 => simp [arcs_nil]
  | h1 x => simp [arcs_singleton]
  | h2 x y ys ih =>
    rw [arcs_cons_cons_l, List.pairwise_cons]
    rw [List.pairwise_cons] at hR
    exact ⟨fun e he => hR.1 e.1 (mem_arcs he).1, ih hR.2⟩

/-- The arcs of `R` selected by `c` (whose arcs have both ends in `U`) are those of the pieces
of `R` in `U`. -/
theorem filter_arcs_pieces {U : Finset V} (c : V × V → Bool)
    (hc : ∀ e, c e = true → e.1 ∈ U ∧ e.2 ∈ U) (R : List V) :
    (arcs R).filter c = (pieces U R).flatMap (fun r => (arcs r).filter c) := by
  induction R using list_induction2 with
  | h0 => simp [pieces_nil, arcs_nil]
  | h1 x =>
    by_cases hx : x ∈ U
    · simp [pieces_singleton hx, arcs_singleton]
    · simp [pieces_cons_of_not_mem _ hx, pieces_nil, arcs_singleton]
  | h2 x y ys ih =>
    by_cases hx : x ∈ U
    · by_cases hy : y ∈ U
      · obtain ⟨r, rest, h1, h2⟩ := pieces_cons_cons_of_mem ys hx hy
        rw [h1, List.flatMap_cons] at ih
        rw [h2, List.flatMap_cons, arcs_cons_cons_l, arcs_cons_cons_l, List.filter_cons,
          List.filter_cons, ih]
        split_ifs <;> simp
      · have hc' : c (x, y) = false := by
          cases h : c (x, y)
          · rfl
          · exact absurd (hc _ h).2 hy
        rw [pieces_cons_cons_of_not_mem ys hx hy, List.flatMap_cons, arcs_cons_cons_l,
          List.filter_cons, hc', ih]
        simp [arcs_singleton]
    · have hc' : c (x, y) = false := by
        cases h : c (x, y)
        · rfl
        · exact absurd (hc _ h).1 hx
      rw [pieces_cons_of_not_mem _ hx, arcs_cons_cons_l, List.filter_cons, hc', ← ih]
      simp

end Arcs

/-! ### Chains and runs -/

section Chains

variable {k : ℕ}

/-- The demand `(l, first vertex, last vertex)` of a non-empty list. -/
def dem (l : Fin k) (d : V) (r : List V) : Fin k × V × V := (l, r.headD d, r.getLastD d)

/-- Replace the first end of a demand. -/
def setFst (a : V) (σ : Fin k × V × V) : Fin k × V × V := (σ.1, a, σ.2.2)

/-- A non-empty list inside `A ∪ B` (disjoint), cut at its arcs between `A` and `B`, gives the
chain of the demands of its pieces in `A` and in `B`.  The first end of the chain is arbitrary. -/
theorem chainL_perm_pieces (l : Fin k) (d : V) (c : V × V → Bool) :
    ∀ (xs : List V) (A B : Finset V) (x a : V), (∀ v, v ∈ A → v ∉ B) →
      (∀ u v, (u ∈ A ∨ u ∈ B) → (v ∈ A ∨ v ∈ B) →
        (c (u, v) = true ↔ (u ∈ A ∧ v ∈ B ∨ u ∈ B ∧ v ∈ A))) →
      x ∈ A → (∀ v ∈ xs, v ∈ A ∨ v ∈ B) →
      (chainL l a ((arcs (x :: xs)).filter c) ((x :: xs).getLastD d)).Perm
        (((pieces A (x :: xs)).map (dem l d)).modifyHead (setFst a) ++
          (pieces B (x :: xs)).map (dem l d)) := by
  intro xs
  induction xs with
  | nil =>
    intro A B x a hd _ hx _
    simp [arcs_singleton, chainL, pieces_singleton hx, pieces_cons_of_not_mem _ (hd x hx),
      pieces_nil, dem, setFst]
  | cons y ys ih =>
    intro A B x a hd hc hx hxs
    have hys : ∀ v ∈ ys, v ∈ A ∨ v ∈ B := fun v hv => hxs v (List.mem_cons_of_mem _ hv)
    have hxB : x ∉ B := hd x hx
    have hlast : (x :: y :: ys).getLastD d = (y :: ys).getLastD d := by simp
    rcases hxs y (by simp) with hy | hy
    · -- same side: the arc `(x, y)` is not cut
      have hc' : c (x, y) = false := by
        cases h : c (x, y)
        · rfl
        · rcases (hc x y (Or.inl hx) (Or.inl hy)).1 h with h' | h'
          · exact absurd h'.2 (hd y hy)
          · exact absurd h'.1 hxB
      have := ih A B y a hd hc hy hys
      obtain ⟨r, rest, h1, h2⟩ := pieces_cons_cons_of_mem ys hx hy
      rw [arcs_cons_cons_l, List.filter_cons, hc', hlast, h2, pieces_cons_of_not_mem _ hxB]
      rw [h1] at this
      simpa [dem, setFst] using this
    · -- the arc `(x, y)` is cut
      have hc' : c (x, y) = true := (hc x y (Or.inl hx) (Or.inr hy)).2 (Or.inl ⟨hx, hy⟩)
      have hyA : y ∉ A := fun h => hd y h hy
      have := ih B A y y (fun v hv hv' => hd v hv' hv)
        (fun u v hu hv => by rw [hc u v hu.symm hv.symm]; tauto) hy
        (fun v hv => (hys v hv).symm)
      obtain ⟨r, rest, h1, -⟩ := pieces_cons_of_mem (U := B) ys hy
      rw [h1] at this
      rw [arcs_cons_cons_l, List.filter_cons, hc', hlast, pieces_cons_cons_of_not_mem ys hx hyA,
        pieces_cons_of_not_mem _ hxB, h1]
      simp only [ite_true, List.map_cons, List.modifyHead_cons, chainL, List.cons_append]
      refine List.Perm.cons _ ?_
      refine this.trans ?_
      simp only [List.modifyHead_cons, List.map_cons, List.cons_append]
      have e : setFst y (dem l d (y :: r)) = dem l d (y :: r) := by simp [setFst, dem]
      rw [e, ← List.cons_append, ← List.map_cons]
      exact List.perm_append_comm

/-- The chain of a non-empty list inside `A ∪ B`, as a multiset of demands. -/
theorem chainL_pieces (l : Fin k) (d : V) (c : V × V → Bool) {A B : Finset V}
    (hd : ∀ v, v ∈ A → v ∉ B)
    (hc : ∀ u v, (u ∈ A ∨ u ∈ B) → (v ∈ A ∨ v ∈ B) →
      (c (u, v) = true ↔ (u ∈ A ∧ v ∈ B ∨ u ∈ B ∧ v ∈ A)))
    {p : List V} (hp : p ≠ []) (hpU : ∀ v ∈ p, v ∈ A ∨ v ∈ B) :
    (chainL l (p.headD d) ((arcs p).filter c) (p.getLastD d) : Multiset (Fin k × V × V)) =
      ((pieces A p).map (dem l d) : Multiset _) + ((pieces B p).map (dem l d) : Multiset _) := by
  obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hp
  have hxs : ∀ v ∈ xs, v ∈ A ∨ v ∈ B := fun v hv => hpU v (List.mem_cons_of_mem _ hv)
  rcases hpU x (by simp) with hx | hx
  · have := chainL_perm_pieces l d c xs A B x x hd hc hx hxs
    obtain ⟨r, rest, h1, -⟩ := pieces_cons_of_mem (U := A) xs hx
    rw [h1] at this ⊢
    rw [Multiset.coe_add, Multiset.coe_eq_coe]
    simpa [setFst, dem] using this
  · have := chainL_perm_pieces l d c xs B A x x (fun v hv hv' => hd v hv' hv)
      (fun u v hu hv => by rw [hc u v hu.symm hv.symm]; tauto) hx
      (fun v hv => (hxs v hv).symm)
    obtain ⟨r, rest, h1, -⟩ := pieces_cons_of_mem (U := B) xs hx
    rw [h1] at this ⊢
    rw [add_comm, Multiset.coe_add, Multiset.coe_eq_coe]
    simpa [setFst, dem] using this

end Chains

end DSPP
