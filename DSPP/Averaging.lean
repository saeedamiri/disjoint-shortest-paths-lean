/-
The averaging lemma (lem:averaging) and the good level (cor:goodlevel), in a discrete form
without integrals (see `DEVIATIONS.md`).

Paper: "Directed k Disjoint Shortest Paths Is Polynomial for Every Fixed k" (Saeed Amiri),
Section "The cut hierarchy", subsection "The averaging lemma".
-/
import DSPP.Hierarchy

open Classical

namespace DSPP

/-- The measure step of cor:goodlevel, without measure theory.  A finite family of open
intervals (given by unordered end points `a s`, `b s`) of total length less than
`(c + 1) (hi - lo)` leaves a point of `(lo, hi)`, outside any given finite set, that lies in at
most `c` of the intervals. -/
theorem exists_low_count {ι : Type*} (S : Finset ι) (a b : ι → ℝ) (lo hi : ℝ) (c : ℕ)
    (bad : Finset ℝ) (hlt : lo < hi)
    (hsum : ∑ s ∈ S, |b s - a s| < (c + 1) * (hi - lo)) :
    ∃ x, lo < x ∧ x < hi ∧ x ∉ bad ∧
      (S.filter fun s => min (a s) (b s) < x ∧ x < max (a s) (b s)).card ≤ c := by
  open MeasureTheory in
  by_contra hcon
  push Not at hcon
  let I : ι → Set ℝ := fun s => Set.Ioo (min (a s) (b s)) (max (a s) (b s))
  let f : ℝ → ENNReal := fun x => ∑ s ∈ S, (I s).indicator 1 x
  have hcard : ∀ x, ((S.filter fun s => min (a s) (b s) < x ∧ x < max (a s) (b s)).card :
      ENNReal) = f x := by
    intro x
    rw [Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun s _ => ?_
    by_cases h : min (a s) (b s) < x ∧ x < max (a s) (b s)
    · simp only [Set.indicator_of_mem (show x ∈ I s from h), if_pos h, Pi.one_apply]
    · simp only [Set.indicator_of_notMem (show x ∉ I s from h), if_neg h]
  have hup : ∫⁻ x in Set.Ioo lo hi, f x ≤ ∑ s ∈ S, ENNReal.ofReal |b s - a s| := by
    rw [lintegral_finsetSum _ (fun s _ => measurable_one.indicator measurableSet_Ioo)]
    gcongr with s hs
    rw [lintegral_indicator_one measurableSet_Ioo]
    refine (Measure.restrict_apply_le _ _).trans ?_
    rw [Real.volume_Ioo, max_sub_min_eq_abs', abs_sub_comm]
  have hlow : ∫⁻ _ in Set.Ioo lo hi, ((c : ENNReal) + 1) ≤ ∫⁻ x in Set.Ioo lo hi, f x := by
    apply lintegral_mono_ae
    have hnull : ∀ᵐ x ∂(volume : Measure ℝ), x ∉ (bad : Set ℝ) :=
      measure_eq_zero_iff_ae_notMem.mp (bad.finite_toSet.measure_zero _)
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [hnull] with x hx hxI
    rw [← hcard]
    have := hcon x hxI.1 hxI.2 hx
    exact_mod_cast this
  rw [setLIntegral_const, Real.volume_Ioo] at hlow
  have h2 := hlow.trans hup
  rw [← ENNReal.ofReal_sum_of_nonneg (fun s _ => abs_nonneg _),
    show ((c : ENNReal) + 1) = ENNReal.ofReal ((c : ℝ) + 1) by
      rw [ENNReal.ofReal_add (by positivity) zero_le_one]; simp,
    ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg fun s _ => abs_nonneg _)] at h2
  linarith


variable {k : ℕ} [NeZero k] {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Cells: extents of star coordinates -/

/-- The extent of a star coordinate is the difference of the bounds (lem:extent (b)). -/
theorem Cell.ext_star (C : Cell k) (j : StarIdx k) : C.ext 0 j.1 = C.hi j - C.lo j :=
  (Cell.lem_extent_b C).1 j

/-- Every star coordinate has extent at most the width. -/
theorem Cell.bound_le_width (C : Cell k) (j : StarIdx k) :
    C.hi j - C.lo j ≤ C.width := by
  rw [← C.ext_star j]
  exact le_ciSup (f := fun j : StarIdx k => C.ext 0 j.1) (Set.finite_range _).bddAbove j

/-- The lower bound of `X_{1i}` on a cell, for any index `i` (`0` for `i = 1`). -/
noncomputable def Cell.starLo (C : Cell k) (i : Fin k) : ℝ :=
  if h : i = 0 then 0 else C.lo ⟨i, h⟩

/-- The upper bound of `X_{1i}` on a cell, for any index `i` (`0` for `i = 1`). -/
noncomputable def Cell.starHi (C : Cell k) (i : Fin k) : ℝ :=
  if h : i = 0 then 0 else C.hi ⟨i, h⟩

theorem Cell.starLo_le {C : Cell k} {x : Fin k → ℝ} (hx : x ∈ C.carrier) (i : Fin k) :
    C.starLo i ≤ X 0 i x ∧ X 0 i x ≤ C.starHi i := by
  unfold Cell.starLo Cell.starHi
  by_cases h : i = 0
  · subst h; simp [X]
  · rw [dite_cond_eq_false (eq_false h), dite_cond_eq_false (eq_false h)]; exact hx ⟨i, h⟩

theorem Cell.starLo_le_starHi (C : Cell k) (i : Fin k) : C.starLo i ≤ C.starHi i := by
  unfold Cell.starLo Cell.starHi
  by_cases h : i = 0
  · rw [dite_cond_eq_true (eq_true h), dite_cond_eq_true (eq_true h)]
  · rw [dite_cond_eq_false (eq_false h), dite_cond_eq_false (eq_false h)]; exact C.lo_le_hi _

theorem Cell.starHi_sub_starLo_le (C : Cell k) (i : Fin k) (hw : 0 ≤ C.width) :
    C.starHi i - C.starLo i ≤ C.width := by
  unfold Cell.starLo Cell.starHi
  by_cases h : i = 0
  · rw [dite_cond_eq_true (eq_true h), dite_cond_eq_true (eq_true h), sub_self]; exact hw
  · rw [dite_cond_eq_false (eq_false h), dite_cond_eq_false (eq_false h)]; exact C.bound_le_width _

/-! ### Segments and the part of a segment in a cell -/

/-- The point `p + s (q - p)` of the segment from `p` to `q`. -/
noncomputable def segPt (p q : Fin k → ℝ) (s : ℝ) : Fin k → ℝ := p + s • (q - p)

theorem X_segPt (i j : Fin k) (p q : Fin k → ℝ) (s : ℝ) :
    X i j (segPt p q s) = X i j p + s * (X i j q - X i j p) := by
  simp only [segPt, X, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring

/-- The parameters `s ∈ [0, 1]` of the segment from `p` to `q` whose point lies in `C`. -/
noncomputable def segParams (C : Cell k) (p q : Fin k → ℝ) : Set ℝ :=
  Set.Icc 0 1 ∩ segPt p q ⁻¹' C.carrier

theorem isCompact_segParams (C : Cell k) (p q : Fin k → ℝ) : IsCompact (segParams C p q) := by
  apply isCompact_Icc.inter_right
  apply (Cell.lem_extent_a C).2.2.1.preimage
  unfold segPt
  fun_prop

theorem affine_between {A B s0 s s1 lo hi : ℝ} (hs0 : s0 ≤ s) (hs1 : s ≤ s1)
    (h0 : lo ≤ A + s0 * B ∧ A + s0 * B ≤ hi) (h1 : lo ≤ A + s1 * B ∧ A + s1 * B ≤ hi) :
    lo ≤ A + s * B ∧ A + s * B ≤ hi := by
  rcases le_total 0 B with hB | hB
  · have e1 : s0 * B ≤ s * B := mul_le_mul_of_nonneg_right hs0 hB
    have e2 : s * B ≤ s1 * B := mul_le_mul_of_nonneg_right hs1 hB
    constructor <;> linarith [h0.1, h1.2]
  · have e1 : s * B ≤ s0 * B := mul_le_mul_of_nonpos_right hs0 hB
    have e2 : s1 * B ≤ s * B := mul_le_mul_of_nonpos_right hs1 hB
    constructor <;> linarith [h0.2, h1.1]

/-- The parameter set is an interval. -/
theorem mem_segParams_of_between {C : Cell k} {p q : Fin k → ℝ} {s0 s1 s : ℝ}
    (h0 : s0 ∈ segParams C p q) (h1 : s1 ∈ segParams C p q) (hs0 : s0 ≤ s) (hs1 : s ≤ s1) :
    s ∈ segParams C p q := by
  obtain ⟨⟨h00, h01⟩, hc0⟩ := h0
  obtain ⟨⟨h10, h11⟩, hc1⟩ := h1
  refine ⟨⟨by linarith, by linarith⟩, ?_⟩
  intro j
  have a0 : C.lo j ≤ X 0 j.1 (segPt p q s0) ∧ X 0 j.1 (segPt p q s0) ≤ C.hi j := hc0 j
  have a1 : C.lo j ≤ X 0 j.1 (segPt p q s1) ∧ X 0 j.1 (segPt p q s1) ≤ C.hi j := hc1 j
  show C.lo j ≤ X 0 j.1 (segPt p q s) ∧ X 0 j.1 (segPt p q s) ≤ C.hi j
  rw [X_segPt] at a0 a1 ⊢
  exact affine_between hs0 hs1 a0 a1

theorem segParams_facts {C : Cell k} {p q : Fin k → ℝ} (hne : (segParams C p q).Nonempty) :
    sInf (segParams C p q) ∈ segParams C p q ∧ sSup (segParams C p q) ∈ segParams C p q ∧
    ∀ s ∈ segParams C p q, sInf (segParams C p q) ≤ s ∧ s ≤ sSup (segParams C p q) := by
  have hK := isCompact_segParams C p q
  exact ⟨hK.sInf_mem hne, hK.sSup_mem hne,
    fun s hs => ⟨csInf_le hK.bddBelow hs, le_csSup hK.bddAbove hs⟩⟩

/-- The value of `X_{1j}` at the first point of the segment in `C` (`0` if there is none). -/
noncomputable def endA (C : Cell k) (j : StarIdx k) (p q : Fin k → ℝ) : ℝ :=
  if (segParams C p q).Nonempty then X 0 j.1 (segPt p q (sInf (segParams C p q))) else 0

/-- The value of `X_{1j}` at the last point of the segment in `C` (`0` if there is none). -/
noncomputable def endB (C : Cell k) (j : StarIdx k) (p q : Fin k → ℝ) : ℝ :=
  if (segParams C p q).Nonempty then X 0 j.1 (segPt p q (sSup (segParams C p q))) else 0

theorem lt_min_max_of_between {x y z : ℝ} (h1 : min x y ≤ z) (h2 : z ≤ max x y) (hx : z ≠ x)
    (hy : z ≠ y) : min x y < z ∧ z < max x y := by
  constructor
  · refine lt_of_le_of_ne h1 fun h => ?_
    rcases min_choice x y with h' | h' <;> rw [h'] at h
    · exact hx h.symm
    · exact hy h.symm
  · refine lt_of_le_of_ne h2 fun h => ?_
    rcases max_choice x y with h' | h' <;> rw [h'] at h
    · exact hx h
    · exact hy h

/-- An arc is counted in `N_C(λ)` iff `λ` lies strictly between the end values of `X_{1j}` on
the part of its segment in `C` (for `λ` different from these end values). -/
theorem segCross_iff (C : Cell k) (j : StarIdx k) (lam : ℝ) (p q : Fin k → ℝ)
    (hA : lam ≠ endA C j p q) (hB : lam ≠ endB C j p q) :
    segCross C j lam p q ↔
      min (endA C j p q) (endB C j p q) < lam ∧ lam < max (endA C j p q) (endB C j p q) := by
  constructor
  · rintro ⟨hstr, hcp⟩
    have hne0 : X 0 j.1 q - X 0 j.1 p ≠ 0 := by
      intro h0
      rcases hstr with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
    set t := (lam - X 0 j.1 p) / (X 0 j.1 q - X 0 j.1 p) with ht
    have hft : X 0 j.1 p + t * (X 0 j.1 q - X 0 j.1 p) = lam := by
      rw [ht, div_mul_cancel₀ _ hne0]; ring
    have ht01 : t ∈ Set.Icc (0 : ℝ) 1 := by
      rcases hstr with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hpos : 0 < X 0 j.1 q - X 0 j.1 p := by linarith
        constructor
        · exact div_nonneg (by linarith) hpos.le
        · rw [div_le_one hpos]; linarith
      · have hneg : X 0 j.1 q - X 0 j.1 p < 0 := by linarith
        constructor
        · exact div_nonneg_of_nonpos (by linarith) hneg.le
        · rw [div_le_one_of_neg hneg]; linarith
    have htJ : t ∈ segParams C p q := Set.mem_inter ht01 (Set.mem_preimage.mpr hcp)
    have hne : (segParams C p q).Nonempty := ⟨t, htJ⟩
    obtain ⟨h0, h1, hb⟩ := segParams_facts hne
    obtain ⟨hs0, hs1⟩ := hb t htJ
    have hAe : endA C j p q = X 0 j.1 p + sInf (segParams C p q) * (X 0 j.1 q - X 0 j.1 p) := by
      rw [endA, if_pos hne, X_segPt]
    have hBe : endB C j p q = X 0 j.1 p + sSup (segParams C p q) * (X 0 j.1 q - X 0 j.1 p) := by
      rw [endB, if_pos hne, X_segPt]
    have hbtw := affine_between (A := X 0 j.1 p) (B := X 0 j.1 q - X 0 j.1 p)
      (lo := min (endA C j p q) (endB C j p q))
      (hi := max (endA C j p q) (endB C j p q)) hs0 hs1
      (by rw [← hAe]; exact ⟨min_le_left _ _, le_max_left _ _⟩)
      (by rw [← hBe]; exact ⟨min_le_right _ _, le_max_right _ _⟩)
    rw [hft] at hbtw
    exact lt_min_max_of_between hbtw.1 hbtw.2 hA hB
  · rintro ⟨hlo, hhi⟩
    have hne : (segParams C p q).Nonempty := by
      by_contra hne
      simp only [endA, endB, if_neg hne, min_self, max_self] at hlo hhi
      linarith
    obtain ⟨h0, h1, hb⟩ := segParams_facts hne
    have hs01 := (hb _ h0).2
    have h0' := h0
    have h1' := h1
    obtain ⟨⟨h00, h01⟩, -⟩ := h0'
    obtain ⟨⟨h10, h11⟩, -⟩ := h1'
    rw [endA, endB, if_pos hne, if_pos hne, X_segPt, X_segPt] at hlo hhi
    set s0 := sInf (segParams C p q)
    set s1 := sSup (segParams C p q)
    set B := X 0 j.1 q - X 0 j.1 p with hBdef
    rcases lt_trichotomy B 0 with hB | hB | hB
    · -- decreasing
      have e01 : s1 * B ≤ s0 * B := mul_le_mul_of_nonpos_right hs01 hB.le
      have e01' : X 0 j.1 p + s1 * B ≤ X 0 j.1 p + s0 * B := by linarith
      rw [min_eq_right e01'] at hlo; rw [max_eq_left e01'] at hhi
      have hp0 : s0 * B ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h00 hB.le
      have hp1 : B ≤ s1 * B := by nlinarith
      set t := (lam - X 0 j.1 p) / B with ht
      have htB : t * B = lam - X 0 j.1 p := by rw [ht, div_mul_cancel₀ _ hB.ne]
      have hts0 : s0 ≤ t := by
        by_contra h; push Not at h
        have : s0 * B < t * B := mul_lt_mul_of_neg_right h hB
        linarith
      have hts1 : t ≤ s1 := by
        by_contra h; push Not at h
        have : t * B < s1 * B := mul_lt_mul_of_neg_right h hB
        linarith
      have htJ := mem_segParams_of_between h0 h1 hts0 hts1
      refine ⟨Or.inr ⟨by linarith, by linarith⟩, ?_⟩
      exact htJ.2
    · rw [hB] at hlo hhi
      simp only [mul_zero, add_zero, min_self, max_self] at hlo hhi
      linarith
    · -- increasing
      have e01 : s0 * B ≤ s1 * B := mul_le_mul_of_nonneg_right hs01 hB.le
      have e01' : X 0 j.1 p + s0 * B ≤ X 0 j.1 p + s1 * B := by linarith
      rw [min_eq_left e01'] at hlo; rw [max_eq_right e01'] at hhi
      have hp0 : 0 ≤ s0 * B := mul_nonneg h00 hB.le
      have hp1 : s1 * B ≤ B := by nlinarith
      set t := (lam - X 0 j.1 p) / B with ht
      have htB : t * B = lam - X 0 j.1 p := by rw [ht, div_mul_cancel₀ _ hB.ne']
      have hts0 : s0 ≤ t := by
        by_contra h; push Not at h
        have : t * B < s0 * B := mul_lt_mul_of_pos_right h hB
        linarith
      have hts1 : t ≤ s1 := by
        by_contra h; push Not at h
        have : s1 * B < t * B := mul_lt_mul_of_pos_right h hB
        linarith
      have htJ := mem_segParams_of_between h0 h1 hts0 hts1
      refine ⟨Or.inl ⟨by linarith, by linarith⟩, ?_⟩
      exact htJ.2

/-- The length of the interval of one arc is at most the increase of a clipped monotone
functional `h` along the arc. -/
theorem abs_endB_sub_endA_le (C : Cell k) (j : StarIdx k) (p q : Fin k → ℝ)
    (h : (Fin k → ℝ) → ℝ) (haff : ∀ s, h (segPt p q s) = h p + s * (h q - h p))
    (m M : ℝ) (hmM : ∀ x ∈ C.carrier, m ≤ h x ∧ h x ≤ M)
    (hmono : |X 0 j.1 q - X 0 j.1 p| ≤ h q - h p) :
    |endB C j p q - endA C j p q| ≤ min (max (h q) m) M - min (max (h p) m) M := by
  have hd : 0 ≤ h q - h p := le_trans (abs_nonneg _) hmono
  by_cases hne : (segParams C p q).Nonempty
  · obtain ⟨h0, h1, hb⟩ := segParams_facts hne
    have hs01 := (hb _ h0).2
    rw [endA, endB, if_pos hne, if_pos hne, X_segPt, X_segPt]
    have hm0 := hmM _ h0.2
    have hm1 := hmM _ h1.2
    rw [haff] at hm0 hm1
    set s0 := sInf (segParams C p q)
    set s1 := sSup (segParams C p q)
    have e : X 0 j.1 p + s1 * (X 0 j.1 q - X 0 j.1 p) - (X 0 j.1 p + s0 * (X 0 j.1 q - X 0 j.1 p))
        = (s1 - s0) * (X 0 j.1 q - X 0 j.1 p) := by ring
    rw [e, abs_mul, abs_of_nonneg (sub_nonneg.mpr hs01 : (0 : ℝ) ≤ s1 - s0)]
    have k1 : (s1 - s0) * |X 0 j.1 q - X 0 j.1 p| ≤ (s1 - s0) * (h q - h p) :=
      mul_le_mul_of_nonneg_left hmono (by linarith)
    have k2 : 0 ≤ s0 * (h q - h p) := mul_nonneg h0.1.1 hd
    have k3 : s1 * (h q - h p) ≤ h q - h p := by nlinarith [h1.1.2]
    have c1 : min (max (h p) m) M ≤ h p + s0 * (h q - h p) :=
      min_le_of_left_le (max_le (by linarith) hm0.1)
    have c2 : h p + s1 * (h q - h p) ≤ min (max (h q) m) M :=
      le_min (le_max_of_le_left (by linarith)) hm1.2
    have e2 : (s1 - s0) * (h q - h p) = s1 * (h q - h p) - s0 * (h q - h p) := by ring
    linarith
  · rw [endA, endB, if_neg hne, if_neg hne, sub_self, abs_zero, sub_nonneg]
    exact min_le_min (max_le_max (by linarith) le_rfl) le_rfl

/-! ### Lists of arcs -/

theorem arcs_cons_cons {α : Type*} (v w : α) (r : List α) :
    arcs (v :: w :: r) = (v, w) :: arcs (w :: r) := rfl

theorem rel_of_mem_arcs {α : Type*} {r : α → α → Prop} :
    ∀ {R : List α}, R.IsChain r → ∀ e ∈ arcs R, r e.1 e.2
  | [], _, e, he => by simp [arcs] at he
  | [_], _, e, he => by simp [arcs] at he
  | v :: w :: R, h, e, he => by
    rw [arcs_cons_cons, List.mem_cons] at he
    rw [List.isChain_cons_cons] at h
    rcases he with rfl | he
    · exact h.1
    · exact rel_of_mem_arcs h.2 e he

/-- Telescoping along a list of arcs, for a function with values in `[m, M]`. -/
theorem sum_arcs_le {α : Type*} (R : List α) (F : α × α → ℝ) (g : α → ℝ) (m M : ℝ)
    (hmM : m ≤ M) (hg : ∀ v, m ≤ g v ∧ g v ≤ M) (hF : ∀ e ∈ arcs R, F e ≤ g e.2 - g e.1) :
    ((arcs R).map F).sum ≤ M - m := by
  have aux : ∀ (r : List α) (v : α), (∀ e ∈ arcs (v :: r), F e ≤ g e.2 - g e.1) →
      ((arcs (v :: r)).map F).sum ≤ M - g v := by
    intro r
    induction r with
    | nil => intro v _; simp [arcs]; linarith [hg v]
    | cons w r ih =>
      intro v hF'
      rw [arcs_cons_cons, List.map_cons, List.sum_cons]
      have h1 : F (v, w) ≤ g w - g v := hF' (v, w) (by rw [arcs_cons_cons]; simp)
      have h2 := ih w (fun e he => hF' e (by rw [arcs_cons_cons]; simp [he]))
      linarith
  cases R with
  | nil => simp [arcs]; linarith
  | cons v r => linarith [aux r v hF, hg v]

theorem length_filter_eq_sum {α : Type*} (L : List α) (p : α → Prop) :
    (L.filter fun e => decide (p e)).length = (L.map fun e => if p e then 1 else 0).sum := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    by_cases h : p a
    · simp [List.filter_cons, h, ih] <;> omega
    · simp [List.filter_cons, h, ih] <;> omega

namespace Instance

variable (G : Instance V k)

/-- The functional `X_{l1} + X_{lj}` is monotone along the arcs of `D_l` and dominates the
change of `X_{1j}` (lem:W12 (W1)). -/
theorem abs_X_le_of_inD {l : Fin k} {u v : V} (huv : G.inD l u v) (j : StarIdx k) :
    |X 0 j.1 (G.pt v) - X 0 j.1 (G.pt u)| ≤
      (X l 0 (G.pt v) + X l j.1 (G.pt v)) - (X l 0 (G.pt u) + X l j.1 (G.pt u)) := by
  obtain ⟨h1, h2⟩ := G.lem_W1 huv
  simp only [Instance.Xv] at h1 h2
  have eXX : ∀ (i : Fin k) (x : Fin k → ℝ), X i i x = 0 := fun i x => by simp [X]
  by_cases hl0 : l = 0
  · subst hl0
    have := h1 j.1 j.2
    simp only [eXX, zero_add]
    exact (abs_of_nonneg this).le
  · by_cases hlj : l = j.1
    · subst hlj
      have := h1 0 (fun h => j.2 h.symm)
      simp only [eXX, add_zero]
      have e : ∀ x, X 0 j.1 x = - X j.1 0 x := fun x => by simp [X]
      rw [e, e, show -X j.1 0 (G.pt v) - -X j.1 0 (G.pt u) =
        -(X j.1 0 (G.pt v) - X j.1 0 (G.pt u)) by ring, abs_neg]
      exact (abs_of_nonneg this).le
    · exact (h2 0 j.1 (fun h => hl0 h.symm) (fun h => hlj h.symm)).trans (le_of_eq (by ring))

/-- The bound on the total length of the intervals of path `l`. -/
noncomputable def pathBd (C : Cell k) (j : StarIdx k) (l : Fin k) : ℝ :=
  if l = j.1 then C.hi j - C.lo j else 2 * (C.starHi l - C.starLo l) + (C.hi j - C.lo j)

/-- lem:averaging, the bound for one path. -/
theorem path_bound (C : Cell k) (j : StarIdx k) {l : Fin k} {R : List V} (hR : G.IsDPath l R) :
    ((arcs R).map fun e => |endB C j (G.pt e.1) (G.pt e.2) - endA C j (G.pt e.1) (G.pt e.2)|).sum
      ≤ pathBd C j l := by
  set h : (Fin k → ℝ) → ℝ := fun x => X l 0 x + X l j.1 x with hh
  have haff : ∀ p q s, h (segPt p q s) = h p + s * (h q - h p) := by
    intro p q s; simp only [hh, X_segPt]; ring
  have hX : ∀ x, h x = -2 * X 0 l x + X 0 j.1 x := by intro x; simp only [hh, X]; ring
  obtain ⟨m, M, hmM, hrange, hbd⟩ : ∃ m M : ℝ, m ≤ M ∧
      (∀ x ∈ C.carrier, m ≤ h x ∧ h x ≤ M) ∧ M - m ≤ pathBd C j l := by
    unfold pathBd
    by_cases hlj : l = j.1
    · refine ⟨-C.hi j, -C.lo j, by linarith [C.lo_le_hi j], fun x hx => ?_,
        by rw [if_pos hlj]; linarith⟩
      have h1 : C.lo j ≤ X 0 j.1 x ∧ X 0 j.1 x ≤ C.hi j := hx j
      rw [hX, hlj]; constructor <;> linarith [h1.1, h1.2]
    · refine ⟨C.lo j - 2 * C.starHi l, C.hi j - 2 * C.starLo l,
        by linarith [C.lo_le_hi j, C.starLo_le_starHi l], fun x hx => ?_,
        by rw [if_neg hlj]; linarith⟩
      have h1 : C.lo j ≤ X 0 j.1 x ∧ X 0 j.1 x ≤ C.hi j := hx j
      have h2 := C.starLo_le hx l
      rw [hX]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  refine le_trans ?_ hbd
  exact sum_arcs_le R _ (fun v => min (max (h (G.pt v)) m) M) m M hmM
    (fun v => ⟨le_min (le_max_right _ _) hmM, min_le_right _ _⟩)
    (fun e he => abs_endB_sub_endA_le C j _ _ h (haff _ _) m M hrange
      (G.abs_X_le_of_inD (rel_of_mem_arcs hR.2.1 e he) j))

end Instance

/-- The bounds of the paths add up to `(3k - 4) E`. -/
theorem sum_pathBd (C : Cell k) (j : StarIdx k) (hE : 0 < C.width)
    (hj : C.ext 0 j.1 = C.width) :
    ∑ l, Instance.pathBd C j l ≤ (3 * (k : ℝ) - 4) * C.width := by
  have hwj : C.hi j - C.lo j = C.width := by rw [← C.ext_star j, hj]
  have hj0 : j.1 ≠ 0 := j.2
  calc ∑ l, Instance.pathBd C j l
      ≤ ∑ l : Fin k, (3 * C.width - (if l = 0 then 2 * C.width else 0) -
          (if l = j.1 then 2 * C.width else 0)) := by
        refine Finset.sum_le_sum fun l _ => ?_
        unfold Instance.pathBd
        by_cases hlj : l = j.1
        · have hl0 : l ≠ 0 := by rw [hlj]; exact hj0
          rw [if_pos hlj, if_neg hl0, if_pos hlj, hwj]; linarith
        · rw [if_neg hlj, if_neg hlj, hwj]
          by_cases hl0 : l = 0
          · rw [if_pos hl0]
            subst hl0
            have e0 : C.starHi 0 - C.starLo 0 = 0 := by simp [Cell.starHi, Cell.starLo]
            rw [e0]
            linarith
          · rw [if_neg hl0]
            have := C.starHi_sub_starLo_le l hE.le
            linarith
    _ = (3 * (k : ℝ) - 4) * C.width := by
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
        ring

namespace Instance

variable (G : Instance V k)

/-- lem:averaging (discrete form).  Let `C` be a cell of width `E > 0` and `X_{1j}` a widest
star coordinate.  Then, for all generic `λ` outside a finite set, `N_C(λ)` is the number of
intervals of a finite family `(a s, b s)` that contain `λ` (a step function), and the total
length of the family (the integral of the step function) is at most `(3k - 4) E`. -/
theorem lem_averaging (Rs : Fin k → List V) (hRs : ∀ l, G.IsDPath l (Rs l))
    (C : Cell k) (j : StarIdx k) (hE : 0 < C.width) (hj : C.ext 0 j.1 = C.width) :
    ∃ (N : ℕ) (a b : Fin N → ℝ) (bad : Finset ℝ),
      ∑ s, |b s - a s| ≤ (3 * (k : ℝ) - 4) * C.width ∧
      ∀ lam, G.IsGeneric j lam → lam ∉ bad →
        G.crossNum Rs C j lam =
          (Finset.univ.filter fun s => min (a s) (b s) < lam ∧ lam < max (a s) (b s)).card := by
  let A : (Σ l : Fin k, Fin (arcs (Rs l)).length) → ℝ := fun x =>
    endA C j (G.pt ((arcs (Rs x.1))[x.2.1]'x.2.2).1) (G.pt ((arcs (Rs x.1))[x.2.1]'x.2.2).2)
  let B : (Σ l : Fin k, Fin (arcs (Rs l)).length) → ℝ := fun x =>
    endB C j (G.pt ((arcs (Rs x.1))[x.2.1]'x.2.2).1) (G.pt ((arcs (Rs x.1))[x.2.1]'x.2.2).2)
  let e := Fintype.equivFin (Σ l : Fin k, Fin (arcs (Rs l)).length)
  refine ⟨Fintype.card (Σ l : Fin k, Fin (arcs (Rs l)).length), fun s => A (e.symm s),
    fun s => B (e.symm s), Finset.univ.image A ∪ Finset.univ.image B, ?_, ?_⟩
  · refine (Equiv.sum_comp e.symm (fun x => |B x - A x|)).trans_le ?_
    refine (Fintype.sum_sigma _).trans_le ?_
    refine le_trans (Finset.sum_le_sum fun l _ => ?_) (sum_pathBd C j hE hj)
    exact (Fin.sum_univ_fun_getElem (arcs (Rs l)) (fun e =>
      |endB C j (G.pt e.1) (G.pt e.2) - endA C j (G.pt e.1) (G.pt e.2)|)).trans_le
      (G.path_bound C j (hRs l))
  · intro lam _ hbad
    have hA : ∀ x, lam ≠ A x := fun x h =>
      hbad (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, h.symm⟩))
    have hB : ∀ x, lam ≠ B x := fun x h =>
      hbad (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, h.symm⟩))
    rw [Finset.card_filter]
    refine Eq.trans ?_ (Equiv.sum_comp e.symm (fun x =>
      if min (A x) (B x) < lam ∧ lam < max (A x) (B x) then 1 else 0)).symm
    refine Eq.trans ?_ (Fintype.sum_sigma _).symm
    unfold crossNum
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [length_filter_eq_sum, ← Fin.sum_univ_fun_getElem]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hiff := segCross_iff C j lam (G.pt ((arcs (Rs l))[i.1]'i.2).1) (G.pt ((arcs (Rs l))[i.1]'i.2).2)
      (hA ⟨l, i⟩) (hB ⟨l, i⟩)
    by_cases hc : segCross C j lam (G.pt ((arcs (Rs l))[i.1]'i.2).1) (G.pt ((arcs (Rs l))[i.1]'i.2).2)
    · rw [if_pos hc]
      exact (if_pos (hiff.mp hc)).symm
    · rw [if_neg hc]
      exact (if_neg (fun h => hc (hiff.mpr h))).symm

/-- cor:goodlevel.  In the situation of lem:averaging there is a good level: a generic `λ` with
`m + θE ≤ λ ≤ M - θE` and `N_C(λ) ≤ 3k - 4`, where `θ = 1/(6k)` and `[m, M] = [a_j, b_j]` is
the range of `X_{1j}` on `C`. -/
theorem cor_goodlevel (Rs : Fin k → List V) (hRs : ∀ l, G.IsDPath l (Rs l))
    (C : Cell k) (j : StarIdx k) (hE : 0 < C.width) (hj : C.ext 0 j.1 = C.width) :
    ∃ lam, G.IsGoodLevel Rs C j lam := by
  obtain ⟨N, a, b, bad, hsum, hcount⟩ := G.lem_averaging Rs hRs C j hE hj
  have hk2 : 2 ≤ k := by
    by_contra h
    have hk1 : k = 1 := by have := NeZero.ne k; omega
    subst hk1
    exact j.2 (Subsingleton.elim _ _)
  have hwj : C.hi j - C.lo j = C.width := by rw [← C.ext_star j, hj]
  have hk : (2 : ℝ) ≤ k := by exact_mod_cast hk2
  have hk0 : (k : ℝ) ≠ 0 := ne_of_gt (by linarith)
  have hθ : theta k * (6 * k) = 1 := by unfold theta; field_simp
  have hθpos : 0 < theta k := by unfold theta; exact div_pos one_pos (by linarith)
  have hθ12 : theta k ≤ 1 / 12 := by nlinarith
  have hθE : theta k * C.width ≤ C.width / 12 := by nlinarith
  have hc : (((3 * k - 4 : ℕ) : ℝ)) = 3 * (k : ℝ) - 4 := by
    rw [Nat.cast_sub (show 4 ≤ 3 * k by omega), Nat.cast_mul]; norm_num
  obtain ⟨x, hx1, hx2, hxbad, hxc⟩ := exists_low_count Finset.univ a b
    (C.lo j + theta k * C.width) (C.hi j - theta k * C.width) (3 * k - 4)
    (bad ∪ Finset.univ.image (G.starX j)) (by linarith) (by
      rw [hc]
      have e : (3 * (k : ℝ) - 4 + 1) * (C.hi j - theta k * C.width -
          (C.lo j + theta k * C.width)) - (3 * (k : ℝ) - 4) * C.width =
          6 * theta k * C.width := by
        rw [← hwj]; linear_combination (-(C.hi j - C.lo j)) * hθ
      have : 0 < 6 * theta k * C.width := by have := mul_pos hθpos hE; linarith
      linarith)
  have hgen : G.IsGeneric j x := fun v hv =>
    hxbad (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨v, Finset.mem_univ _, hv⟩))
  refine ⟨x, hgen, hx1.le, hx2.le, ?_⟩
  rw [hcount x hgen (fun h => hxbad (Finset.mem_union_left _ h))]
  exact hxc

end Instance

end DSPP
