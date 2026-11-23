/-
Few pieces in every cell (lem:pieces).

Paper: "Directed k Disjoint Shortest Paths Is Polynomial for Every Fixed k" (Saeed Amiri),
Section "The cut hierarchy", subsection "Few pieces".

The proof is the charging argument of lem:pieces, done arc by arc (see `DEVIATIONS.md`).  An
arc with exactly one end in `V(C)` is charged to a bound of `C` that is not a bound of the
root: among the bounds violated by the outer end, the one whose level is crossed last on the
arc.  That crossing point lies in `C`, so the arc is counted by the crossing number of the cell
whose cut produced the bound.  There are `2(k-1)` bound types, and every piece that does not
start (end) at the first (last) vertex of its path has an entering (leaving) arc.
-/
import DSPP.Hierarchy

open Classical

namespace DSPP

variable {k : ℕ} [NeZero k] {V : Type*} [Fintype V] [DecidableEq V]

namespace PiecesProof

theorem X_segment (i j : Fin k) (p q : Fin k → ℝ) (c : ℝ) :
    X i j (p + c • (q - p)) = X i j p + c * (X i j q - X i j p) := by
  simp only [X, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring

theorem segment_mem (C : Cell k) {p q : Fin k → ℝ} (hp : p ∈ C.carrier) (hq : q ∈ C.carrier)
    {c : ℝ} (h0 : 0 ≤ c) (h1 : c ≤ 1) : p + c • (q - p) ∈ C.carrier := by
  intro j
  rw [X_segment]
  obtain ⟨a, b⟩ := hp j
  obtain ⟨a', b'⟩ := hq j
  constructor <;> nlinarith [mul_nonneg h0 (sub_nonneg.2 a'), mul_nonneg h0 (sub_nonneg.2 b'),
    mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 a), mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 b)]

theorem lower_carrier_subset (C : Cell k) (j : StarIdx k) (lam : ℝ) (h : lam ≤ C.hi j) :
    (C.lower j lam).carrier ⊆ C.carrier := by
  intro x hx j'
  obtain ⟨a, b⟩ := hx j'
  by_cases hj : j' = j
  · subst hj
    simp only [Cell.lower, Function.update_self] at a b
    exact ⟨a, b.trans (max_le (C.lo_le_hi j') h)⟩
  · simp only [Cell.lower, Function.update_of_ne hj] at a b
    exact ⟨a, b⟩

theorem upper_carrier_subset (C : Cell k) (j : StarIdx k) (lam : ℝ) (h : C.lo j ≤ lam) :
    (C.upper j lam).carrier ⊆ C.carrier := by
  intro x hx j'
  obtain ⟨a, b⟩ := hx j'
  by_cases hj : j' = j
  · subst hj
    simp only [Cell.upper, Function.update_self] at a b
    exact ⟨(le_min (C.lo_le_hi j') h).trans a, b⟩
  · simp only [Cell.upper, Function.update_of_ne hj] at a b
    exact ⟨a, b⟩

theorem crossPt_comm (j : StarIdx k) (lam : ℝ) (p q : Fin k → ℝ) (h : X 0 j.1 p ≠ X 0 j.1 q) :
    crossPt j lam p q = crossPt j lam q p := by
  have h1 : X 0 j.1 q - X 0 j.1 p ≠ 0 := sub_ne_zero.2 (Ne.symm h)
  have h2 : X 0 j.1 p - X 0 j.1 q ≠ 0 := sub_ne_zero.2 h
  funext i
  simp only [crossPt, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  field_simp
  ring

theorem segCross_comm (C : Cell k) (j : StarIdx k) (lam : ℝ) (p q : Fin k → ℝ)
    (h : segCross C j lam p q) : segCross C j lam q p := by
  obtain ⟨hs, hc⟩ := h
  have hne : X 0 j.1 p ≠ X 0 j.1 q := by
    rcases hs with ⟨a, b⟩ | ⟨a, b⟩ <;> intro h <;> linarith
  refine ⟨hs.symm, ?_⟩
  rwa [← crossPt_comm j lam p q hne]

/-- A bound of a cell: `τ = (j, false)` is the lower bound in `X_{1j}`, `τ = (j, true)` the
upper bound. -/
def bnd (C : Cell k) (τ : StarIdx k × Bool) : ℝ := bif τ.2 then C.hi τ.1 else C.lo τ.1

theorem bnd_lower (C : Cell k) (j : StarIdx k) (lam : ℝ) (τ : StarIdx k × Bool) :
    bnd (C.lower j lam) τ = if τ = (j, true) then max (C.lo j) lam else bnd C τ := by
  obtain ⟨j', b⟩ := τ
  by_cases hj : j' = j
  · subst hj; cases b <;> simp [bnd, Cell.lower]
  · cases b <;> simp [bnd, Cell.lower, hj, Function.update_of_ne hj]

theorem bnd_upper (C : Cell k) (j : StarIdx k) (lam : ℝ) (τ : StarIdx k × Bool) :
    bnd (C.upper j lam) τ = if τ = (j, false) then min (C.hi j) lam else bnd C τ := by
  obtain ⟨j', b⟩ := τ
  by_cases hj : j' = j
  · subst hj; cases b <;> simp [bnd, Cell.upper]
  · cases b <;> simp [bnd, Cell.upper, hj, Function.update_of_ne hj]

/-! ### Pieces and boundary arcs -/

/-- The number of non-empty blocks of `R.splitOnP p`. -/
def cnt (p : V → Bool) (R : List V) : ℕ := ((R.splitOnP p).filter fun l => !l.isEmpty).length

theorem splitOnP_head (p : V → Bool) (xs : List V) :
    ∃ h t, xs.splitOnP p = h :: t ∧ (h = [] ↔ ∀ y ∈ xs.head?, p y = true) := by
  cases xs with
  | nil => exact ⟨[], [], by simp⟩
  | cons y ys =>
    by_cases hy : p y = true
    · exact ⟨[], ys.splitOnP p, by rw [List.splitOnP_cons, if_pos hy], by simp [hy]⟩
    · obtain ⟨h, t, ht⟩ : ∃ h t, ys.splitOnP p = h :: t := by
        cases hh : ys.splitOnP p with
        | nil => exact absurd hh (List.splitOnP_ne_nil _ _)
        | cons h t => exact ⟨h, t, rfl⟩
      exact ⟨y :: h, t, by rw [List.splitOnP_cons, if_neg hy, ht]; rfl, by simp [hy]⟩

theorem cnt_cons_sep (p : V → Bool) (x : V) (xs : List V) (hx : p x = true) :
    cnt p (x :: xs) = cnt p xs := by
  unfold cnt
  rw [List.splitOnP_cons, if_pos hx]
  simp [List.filter_cons]

theorem cnt_cons_keep (p : V → Bool) (x : V) (xs : List V) (hx : ¬ p x = true) :
    cnt p (x :: xs) = cnt p xs + (if ∀ y ∈ xs.head?, p y = true then 1 else 0) := by
  obtain ⟨h, t, ht, hiff⟩ := splitOnP_head p xs
  unfold cnt
  rw [List.splitOnP_cons, if_neg hx, ht]
  show (((x :: h) :: t).filter fun l => !l.isEmpty).length =
    ((h :: t).filter fun l => !l.isEmpty).length + _
  by_cases hh : h = []
  · subst hh
    rw [if_pos (hiff.1 rfl)]
    (try simp [List.filter_cons]) <;> omega
  · rw [if_neg (fun h' => hh (hiff.2 h'))]
    (try simp [List.filter_cons, hh]) <;> omega

/-- The number of arcs of `R` with exactly one end in `U`. -/
def bdArcs (U : Finset V) (R : List V) : ℕ :=
  (arcs R).countP fun e => decide ((e.1 ∈ U) ≠ (e.2 ∈ U))

theorem two_mul_cnt_cons (U : Finset V) (x : V) (xs : List V) :
    2 * cnt (fun v => decide (v ∉ U)) (x :: xs) = bdArcs U (x :: xs) +
      (if x ∈ U then 1 else 0) +
      (if (x :: xs).getLast (List.cons_ne_nil x xs) ∈ U then 1 else 0) := by
  induction xs generalizing x with
  | nil =>
    by_cases hx : x ∈ U
    · rw [cnt_cons_keep _ x [] (by simpa using hx)]
      simp [cnt, bdArcs, arcs, hx]
    · rw [cnt_cons_sep _ x [] (by simpa using hx)]
      simp [cnt, bdArcs, arcs, hx]
  | cons y ys ih =>
    have hb : bdArcs U (x :: y :: ys) =
        bdArcs U (y :: ys) + (if (x ∈ U) ≠ (y ∈ U) then 1 else 0) := by
      simp only [bdArcs, arcs, List.tail_cons, List.zip_cons_cons, List.countP_cons]
      simp
    have hl : (x :: y :: ys).getLast (List.cons_ne_nil x (y :: ys)) =
        (y :: ys).getLast (List.cons_ne_nil y ys) := List.getLast_cons_cons
    rw [hb, hl]
    have ih' := ih y
    by_cases hx : x ∈ U
    · rw [cnt_cons_keep _ x _ (by simpa using hx)]
      by_cases hy : y ∈ U <;> simp [hx, hy] at ih' ⊢ <;> omega
    · rw [cnt_cons_sep _ x _ (by simpa using hx)]
      by_cases hy : y ∈ U <;> simp [hx, hy] at ih' ⊢ <;> omega

theorem two_mul_pieces_le (U : Finset V) (R : List V) :
    2 * (pieces U R).length ≤ bdArcs U R + 2 := by
  change 2 * cnt (fun v => decide (v ∉ U)) R ≤ bdArcs U R + 2
  cases R with
  | nil => simp [cnt]
  | cons x xs =>
    rw [two_mul_cnt_cons]
    split_ifs <;> omega

/-- Counting by cases: if every element satisfying `p` satisfies some `q i`, then `p` is
satisfied at most as often as the `q i` together. -/
theorem countP_le_sum_countP {α ι : Type*} [Fintype ι] (L : List α) (p : α → Bool)
    (q : ι → α → Bool) (h : ∀ e ∈ L, p e → ∃ i, q i e) :
    L.countP p ≤ ∑ i, L.countP (q i) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.countP_cons, Finset.sum_add_distrib]
    have ih' := ih fun e he hp => h e (List.mem_cons_of_mem a he) hp
    by_cases hp : p a
    · obtain ⟨i, hi⟩ := h a List.mem_cons_self hp
      have : 1 ≤ ∑ j, (if q j a = true then 1 else 0) :=
        le_trans (by simp [hi]) (Finset.single_le_sum (f := fun j => if q j a = true then 1 else 0)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
      rw [if_pos hp]
      omega
    · rw [if_neg hp]
      omega

/-! ### The violated constraint whose crossing is latest -/

/-- The constraint `τ` of a cell as a linear form: `X_{1j}` for a lower bound, `-X_{1j}` for an
upper bound. -/
def phi (τ : StarIdx k × Bool) (x : Fin k → ℝ) : ℝ := bif τ.2 then -X 0 τ.1.1 x else X 0 τ.1.1 x

/-- The right-hand side of the constraint `τ`: `x ∈ C` iff `beta τ ≤ phi τ x` for all `τ`. -/
def beta (C : Cell k) (τ : StarIdx k × Bool) : ℝ := bif τ.2 then -C.hi τ.1 else C.lo τ.1

theorem mem_carrier_iff (C : Cell k) (x : Fin k → ℝ) :
    x ∈ C.carrier ↔ ∀ τ, beta C τ ≤ phi τ x := by
  constructor
  · intro h τ
    obtain ⟨j, b⟩ := τ
    cases b
    · exact (h j).1
    · exact neg_le_neg (h j).2
  · intro h j
    have h1 := h (j, false)
    have h2 := h (j, true)
    change C.lo j ≤ X 0 j.1 x at h1
    change -C.hi j ≤ -X 0 j.1 x at h2
    exact ⟨h1, by linarith⟩

theorem phi_segment (τ : StarIdx k × Bool) (p q : Fin k → ℝ) (c : ℝ) :
    phi τ (p + c • (q - p)) = phi τ p + c * (phi τ q - phi τ p) := by
  obtain ⟨j, b⟩ := τ
  cases b
  · exact X_segment _ _ p q c
  · show -X 0 j.1 (p + c • (q - p)) = -X 0 j.1 p + c * (-X 0 j.1 q - -X 0 j.1 p)
    rw [X_segment]; ring

/-- If `p ∉ C` and `q ∈ C`, then among the constraints violated by `p` the one whose level is
crossed last on the segment from `p` to `q` is crossed at a point of `C`. -/
theorem exists_entry_constraint (C : Cell k) {p q : Fin k → ℝ} (hp : p ∉ C.carrier)
    (hq : q ∈ C.carrier) :
    ∃ τ, phi τ p < beta C τ ∧
      p + ((beta C τ - phi τ p) / (phi τ q - phi τ p)) • (q - p) ∈ C.carrier := by
  rw [mem_carrier_iff] at hp hq
  push_neg at hp
  obtain ⟨τ0, hτ0⟩ := hp
  let S : Finset (StarIdx k × Bool) := Finset.univ.filter fun τ => phi τ p < beta C τ
  have hS : S.Nonempty := ⟨τ0, by simp [S, hτ0]⟩
  obtain ⟨τ, hτS, hmax⟩ :=
    S.exists_max_image (fun τ => (beta C τ - phi τ p) / (phi τ q - phi τ p)) hS
  have hτ : phi τ p < beta C τ := by simpa [S] using hτS
  refine ⟨τ, hτ, ?_⟩
  have hd : 0 < phi τ q - phi τ p := by linarith [hq τ]
  have hs0 : 0 ≤ (beta C τ - phi τ p) / (phi τ q - phi τ p) := div_nonneg (by linarith) hd.le
  have hs1 : (beta C τ - phi τ p) / (phi τ q - phi τ p) ≤ 1 :=
    (div_le_one hd).2 (by linarith [hq τ])
  rw [mem_carrier_iff]
  intro σ
  rw [phi_segment]
  by_cases hσ : phi σ p < beta C σ
  · have hle := hmax σ (by simp [S, hσ])
    try simp only at hle
    have hdσ : 0 < phi σ q - phi σ p := by linarith [hq σ]
    have hmul : (beta C σ - phi σ p) / (phi σ q - phi σ p) * (phi σ q - phi σ p) =
        beta C σ - phi σ p := div_mul_cancel₀ _ hdσ.ne'
    have := mul_le_mul_of_nonneg_right hle hdσ.le
    linarith
  · push_neg at hσ
    nlinarith [hq σ, mul_nonneg hs0 (sub_nonneg.2 (hq σ)),
      mul_nonneg (sub_nonneg.2 hs1) (sub_nonneg.2 hσ)]

end PiecesProof

open PiecesProof

namespace Instance

variable (G : Instance V k)

/-- The invariant of the cells of a hierarchy with root `R0`: every bound of `C` is a bound of
`R0`, or it is the level of a cut of some cell `A ⊇ C` that is crossed at most `3k - 4` times
(the last half-space of its type). -/
def piecesBoundInv (Rs : Fin k → List V) (R0 C : Cell k) : Prop :=
  ∀ τ : StarIdx k × Bool, bnd C τ = bnd R0 τ ∨
    ∃ A : Cell k, G.IsGeneric τ.1 (bnd C τ) ∧ C.carrier ⊆ A.carrier ∧
      G.crossNum Rs A τ.1 (bnd C τ) ≤ 3 * k - 4

theorem piecesBoundInv_of_mem_nodes (Rs : Fin k → List V) (R0 : Cell k) (T : CutTree k)
    (C0 : Cell k) (hT : G.IsHierarchy T C0)
    (hcut : ∀ C j lam, (C, some (j, lam)) ∈ T.nodes C0 → G.crossNum Rs C j lam ≤ 3 * k - 4)
    (h0 : G.piecesBoundInv Rs R0 C0) :
    ∀ C o, (C, o) ∈ T.nodes C0 → G.piecesBoundInv Rs R0 C := by
  induction T generalizing C0 with
  | leaf =>
    intro C o hC
    simp only [CutTree.nodes, List.mem_singleton, Prod.mk.injEq] at hC
    rw [hC.1]; exact h0
  | node j lam lt rt ihl ihr =>
    obtain ⟨hg, hlo, hhi, hl, hr⟩ := hT
    have hc0 : G.crossNum Rs C0 j lam ≤ 3 * k - 4 := hcut C0 j lam (by simp [CutTree.nodes])
    have hsubL := lower_carrier_subset C0 j lam hhi.le
    have hsubU := upper_carrier_subset C0 j lam hlo.le
    intro C o hC
    simp only [CutTree.nodes, List.mem_cons, List.mem_append, Prod.mk.injEq] at hC
    rcases hC with ⟨rfl, -⟩ | hC | hC
    · exact h0
    · refine ihl (C0.lower j lam) hl
        (fun C' j' lam' h => hcut C' j' lam' (by simp [CutTree.nodes, h])) ?_ C o hC
      intro τ
      rw [bnd_lower]
      split_ifs with hτ
      · subst hτ
        right
        rw [max_eq_right hlo.le]
        exact ⟨C0, hg, hsubL, hc0⟩
      · rcases h0 τ with h | ⟨A, hgA, hsA, hcA⟩
        · exact Or.inl h
        · exact Or.inr ⟨A, hgA, hsubL.trans hsA, hcA⟩
    · refine ihr (C0.upper j lam) hr
        (fun C' j' lam' h => hcut C' j' lam' (by simp [CutTree.nodes, h])) ?_ C o hC
      intro τ
      rw [bnd_upper]
      split_ifs with hτ
      · subst hτ
        right
        rw [min_eq_right hhi.le]
        exact ⟨C0, hg, hsubU, hc0⟩
      · rcases h0 τ with h | ⟨A, hgA, hsA, hcA⟩
        · exact Or.inl h
        · exact Or.inr ⟨A, hgA, hsubU.trans hsA, hcA⟩

/-- An arc entering `C` from a point `p` of the root `R0` crosses the level of some bound of `C`
that is not a bound of `R0`, at a point of `C`; so it is counted by the crossing number of every
cell `A ⊇ C` at that level. -/
theorem pieces_exists_entry (Rs : Fin k → List V) (R0 C : Cell k) (hinv : G.piecesBoundInv Rs R0 C)
    {p : Fin k → ℝ} (hp0 : p ∈ R0.carrier) (hp : p ∉ C.carrier) (v : V)
    (hv : G.pt v ∈ C.carrier) :
    ∃ τ, bnd C τ ≠ bnd R0 τ ∧
      ∀ A : Cell k, C.carrier ⊆ A.carrier → segCross A τ.1 (bnd C τ) p (G.pt v) := by
  obtain ⟨τ, hviol, hmem⟩ := exists_entry_constraint C hp hv
  have hR0 := (mem_carrier_iff R0 p).1 hp0 τ
  have hne : bnd C τ ≠ bnd R0 τ := by
    intro h
    obtain ⟨j, b⟩ := τ
    cases b
    · change C.lo j = R0.lo j at h
      change X 0 j.1 p < C.lo j at hviol
      change R0.lo j ≤ X 0 j.1 p at hR0
      linarith
    · change C.hi j = R0.hi j at h
      change -X 0 j.1 p < -C.hi j at hviol
      change -R0.hi j ≤ -X 0 j.1 p at hR0
      linarith
  obtain ⟨A0, hg, -, -⟩ := (hinv τ).resolve_left hne
  refine ⟨τ, hne, fun A hA => ?_⟩
  have hgv : X 0 τ.1.1 (G.pt v) ≠ bnd C τ := hg v
  have hvC := hv τ.1
  obtain ⟨j, b⟩ := τ
  cases b
  · change X 0 j.1 (G.pt v) ≠ C.lo j at hgv
    change X 0 j.1 p < C.lo j at hviol
    change p + ((C.lo j - X 0 j.1 p) / (X 0 j.1 (G.pt v) - X 0 j.1 p)) • (G.pt v - p)
      ∈ C.carrier at hmem
    exact ⟨Or.inl ⟨hviol, lt_of_le_of_ne hvC.1 hgv.symm⟩, hA hmem⟩
  · change X 0 j.1 (G.pt v) ≠ C.hi j at hgv
    change -X 0 j.1 p < -C.hi j at hviol
    change p + ((-C.hi j - -X 0 j.1 p) / (-X 0 j.1 (G.pt v) - -X 0 j.1 p)) • (G.pt v - p)
      ∈ C.carrier at hmem
    have hc : (-C.hi j - -X 0 j.1 p) / (-X 0 j.1 (G.pt v) - -X 0 j.1 p) =
        (C.hi j - X 0 j.1 p) / (X 0 j.1 (G.pt v) - X 0 j.1 p) := by
      rw [show -C.hi j - -X 0 j.1 p = -(C.hi j - X 0 j.1 p) by ring,
        show -X 0 j.1 (G.pt v) - -X 0 j.1 p = -(X 0 j.1 (G.pt v) - X 0 j.1 p) by ring,
        neg_div_neg_eq]
    rw [hc] at hmem
    exact ⟨Or.inr ⟨lt_of_le_of_ne hvC.2 hgv, by change C.hi j < X 0 j.1 p; linarith⟩, hA hmem⟩

theorem pieces_card_bound_types : Fintype.card (StarIdx k × Bool) = 2 * (k - 1) := by
  rw [Fintype.card_prod, Fintype.card_bool, Fintype.card_subtype, Finset.filter_ne',
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  ring

/-- lem:pieces, pieces part, stated for every hierarchy whose root contains all vertex points
and whose cuts are crossed at most `3k - 4` times (these are the only facts the paper's charging
argument uses; the tree of def:construction has them).  Every cell of the hierarchy contains at
most `P(k)` pieces of `R_1, ..., R_k` in total.  See `DEVIATIONS.md` for the omitted count of
components of `γ_l⁻¹(C)`. -/
theorem lem_pieces (Rs : Fin k → List V) (C0 : Cell k) (T : CutTree k)
    (hT : G.IsHierarchy T C0) (hroot : ∀ v, G.pt v ∈ C0.carrier)
    (hcut : ∀ C j lam, (C, some (j, lam)) ∈ T.nodes C0 → G.crossNum Rs C j lam ≤ 3 * k - 4) :
    ∀ C o, (C, o) ∈ T.nodes C0 → numPieces Rs (G.cellVerts C) ≤ P k := by
  intro C o hC
  have hinv := G.piecesBoundInv_of_mem_nodes Rs C0 T C0 hT hcut (fun _ => Or.inl rfl) C o hC
  -- For each bound type, the cell whose cut produced the bound (if it is not a root bound).
  have hw : ∀ τ : StarIdx k × Bool, ∃ A : Cell k, bnd C τ ≠ bnd C0 τ →
      (G.IsGeneric τ.1 (bnd C τ) ∧ C.carrier ⊆ A.carrier ∧
        G.crossNum Rs A τ.1 (bnd C τ) ≤ 3 * k - 4) := by
    intro τ
    rcases hinv τ with h | ⟨A, hA⟩
    · exact ⟨C, fun h' => absurd h h'⟩
    · exact ⟨A, fun _ => hA⟩
  choose Af hAf using hw
  let q : StarIdx k × Bool → V × V → Bool := fun τ e =>
    decide (bnd C τ ≠ bnd C0 τ ∧ segCross (Af τ) τ.1 (bnd C τ) (G.pt e.1) (G.pt e.2))
  -- Every arc with exactly one end in `V(C)` is charged to a bound type.
  have hpath : ∀ l, bdArcs (G.cellVerts C) (Rs l) ≤ ∑ τ, (arcs (Rs l)).countP (q τ) := by
    intro l
    unfold bdArcs
    apply countP_le_sum_countP
    intro e _ he
    have he' : ¬ ((G.pt e.1 ∈ C.carrier) ↔ (G.pt e.2 ∈ C.carrier)) := by
      intro hiff
      have : (e.1 ∈ G.cellVerts C) = (e.2 ∈ G.cellVerts C) := by
        simp only [cellVerts, Finset.mem_filter, Finset.mem_univ, true_and]
        exact propext hiff
      simp [this] at he
    by_cases h1 : G.pt e.1 ∈ C.carrier
    · have h2 : G.pt e.2 ∉ C.carrier := fun h2 => he' ⟨fun _ => h2, fun _ => h1⟩
      obtain ⟨τ, hne, hseg⟩ := G.pieces_exists_entry Rs C0 C hinv (hroot e.2) h2 e.1 h1
      exact ⟨τ, by
        simp only [q, decide_eq_true_eq]
        exact ⟨hne, segCross_comm _ _ _ _ _ (hseg _ (hAf τ hne).2.1)⟩⟩
    · have h2 : G.pt e.2 ∈ C.carrier := by
        by_contra h2
        exact he' ⟨fun h => absurd h h1, fun h => absurd h h2⟩
      obtain ⟨τ, hne, hseg⟩ := G.pieces_exists_entry Rs C0 C hinv (hroot e.1) h1 e.2 h2
      exact ⟨τ, by
        simp only [q, decide_eq_true_eq]
        exact ⟨hne, hseg _ (hAf τ hne).2.1⟩⟩
  -- Each bound type is charged at most `3k - 4` times.
  have htype : ∀ τ, ∑ l, (arcs (Rs l)).countP (q τ) ≤ 3 * k - 4 := by
    intro τ
    by_cases hne : bnd C τ = bnd C0 τ
    · have : ∀ l, (arcs (Rs l)).countP (q τ) = 0 := fun l =>
        List.countP_eq_zero.2 (fun e _ => by simp [q, hne])
      simp [this]
    · refine le_trans ?_ (hAf τ hne).2.2
      unfold crossNum
      apply Finset.sum_le_sum
      intro l _
      rw [← List.countP_eq_length_filter]
      apply List.countP_mono_left
      intro e _ h
      simp only [q, decide_eq_true_eq] at h ⊢
      exact h.2
  have h2 : 2 * numPieces Rs (G.cellVerts C) ≤ 2 * ((k - 1) * (3 * k - 4)) + 2 * k := by
    unfold numPieces
    rw [Finset.mul_sum]
    calc ∑ l, 2 * (pieces (G.cellVerts C) (Rs l)).length
        ≤ ∑ l : Fin k, (bdArcs (G.cellVerts C) (Rs l) + 2) :=
          Finset.sum_le_sum fun l _ => two_mul_pieces_le _ _
      _ = ∑ l, bdArcs (G.cellVerts C) (Rs l) + 2 * k := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            smul_eq_mul]
          ring
      _ ≤ ∑ l, ∑ τ, (arcs (Rs l)).countP (q τ) + 2 * k := by
          gcongr with l
          exact hpath l
      _ = ∑ τ, ∑ l, (arcs (Rs l)).countP (q τ) + 2 * k := by rw [Finset.sum_comm]
      _ ≤ ∑ _τ : StarIdx k × Bool, (3 * k - 4) + 2 * k := by
          gcongr with τ
          exact htype τ
      _ = 2 * ((k - 1) * (3 * k - 4)) + 2 * k := by
          rw [Finset.sum_const, Finset.card_univ, pieces_card_bound_types, smul_eq_mul]
          ring
  unfold P
  generalize (k - 1) * (3 * k - 4) = m at h2 ⊢
  omega

end Instance

end DSPP
