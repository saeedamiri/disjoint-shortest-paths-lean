/-
Termination of the construction (lem:termination).

Paper: "Directed k Disjoint Shortest Paths Is Polynomial for Every Fixed k" (Saeed Amiri),
Section "The cut hierarchy", subsection "Construction and termination".
-/
import DSPP.Averaging

open Classical

namespace DSPP

variable {k : ℕ} [NeZero k] {V : Type*} [Fintype V] [DecidableEq V]

omit [NeZero k] in
theorem theta_pos_of_pos (hk : 0 < k) : 0 < theta k := by
  unfold theta
  have : (0 : ℝ) < k := by exact_mod_cast hk
  positivity

theorem theta_pos : 0 < theta k := theta_pos_of_pos (Nat.pos_of_ne_zero (NeZero.ne k))

theorem theta_lt_one : theta k < 1 := by
  unfold theta
  have : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne k)
  rw [div_lt_one (by positivity)]
  linarith

/-- The least `n` with `x r^n < δ` (and `0` if there is none). -/
noncomputable def levelIdx (δ r x : ℝ) : ℕ :=
  if h : ∃ n : ℕ, x * r ^ n < δ then Nat.find h else 0

/-- `levelIdx` drops when a value `x ≥ δ` is replaced by a value at most `r x`. -/
theorem levelIdx_lt {δ r x y : ℝ} (hδ : 0 < δ) (hr0 : 0 ≤ r) (hr1 : r < 1) (hx : δ ≤ x)
    (hy : y ≤ r * x) : levelIdx δ r y < levelIdx δ r x := by
  have hxpos : 0 < x := lt_of_lt_of_le hδ hx
  have hex : ∃ n : ℕ, x * r ^ n < δ := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hδ hxpos) hr1
    refine ⟨n, ?_⟩
    calc x * r ^ n < x * (δ / x) := by gcongr
      _ = δ := by field_simp
  have hn0 : Nat.find hex ≠ 0 := by
    intro h0
    have := Nat.find_spec hex
    rw [h0] at this
    simp at this
    linarith
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hspec := Nat.find_spec hex
  rw [hm] at hspec
  have hey : y * r ^ m < δ := by
    calc y * r ^ m ≤ (r * x) * r ^ m := by gcongr
      _ = x * r ^ (m + 1) := by ring
      _ < δ := hspec
  have hey' : ∃ n : ℕ, y * r ^ n < δ := ⟨m, hey⟩
  unfold levelIdx
  rw [dite_cond_eq_true (eq_true hey'), dite_cond_eq_true (eq_true hex), hm]
  exact Nat.lt_succ_of_le (Nat.find_min' hey' hey)

namespace Instance

variable (G : Instance V k)

/-- Vertices of a cell have their star coordinates within the bounds of the cell. -/
theorem starX_mem_bounds {C : Cell k} {v : V} (hv : v ∈ G.cellVerts C) (j : StarIdx k) :
    C.lo j ≤ G.starX j v ∧ G.starX j v ≤ C.hi j := by
  simp only [cellVerts, Finset.mem_filter] at hv
  exact hv.2 j

/-- A cell whose vertex set meets two point classes has two vertices that differ in some star
coordinate. -/
theorem exists_starX_ne (C : Cell k) (hC : ¬ G.AtMostOneClass (G.cellVerts C)) :
    ∃ j : StarIdx k, ∃ u v, u ∈ G.cellVerts C ∧ v ∈ G.cellVerts C ∧
      G.starX j u ≠ G.starX j v := by
  simp only [AtMostOneClass] at hC
  push Not at hC
  obtain ⟨u, hu, v, hv, huv⟩ := hC
  rw [sameClass_iff_star] at huv
  push Not at huv
  obtain ⟨j, hj⟩ := huv
  exact ⟨j, u, v, hu, hv, hj⟩

/-- A positive lower bound on the non-zero differences of star coordinates of vertices. -/
theorem exists_delta : ∃ δ > (0 : ℝ), ∀ (j : StarIdx k) (u v : V),
    G.starX j u ≠ G.starX j v → δ ≤ |G.starX j u - G.starX j v| := by
  let T : Finset ℝ := insert 1 (((Finset.univ : Finset (StarIdx k × V × V)).image
    (fun p => |G.starX p.1 p.2.1 - G.starX p.1 p.2.2|)).filter (0 < ·))
  have hne : T.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  refine ⟨T.min' hne, ?_, ?_⟩
  · rw [gt_iff_lt, Finset.lt_min'_iff]
    intro y hy
    simp only [T, Finset.mem_insert, Finset.mem_filter] at hy
    rcases hy with rfl | ⟨-, hy⟩
    · exact zero_lt_one
    · exact hy
  · intro j u v huv
    apply Finset.min'_le
    simp only [T, Finset.mem_insert, Finset.mem_filter, Finset.mem_image]
    right
    exact ⟨⟨(j, u, v), Finset.mem_univ _, rfl⟩, abs_pos.mpr (sub_ne_zero.mpr huv)⟩

/-- A cell whose vertex set meets two point classes has width at least `δ`. -/
theorem delta_le_of_not_atMostOneClass {δ : ℝ}
    (hδ : ∀ (j : StarIdx k) (u v : V), G.starX j u ≠ G.starX j v →
      δ ≤ |G.starX j u - G.starX j v|)
    (C : Cell k) (hC : ¬ G.AtMostOneClass (G.cellVerts C)) : δ ≤ C.width := by
  obtain ⟨j, u, v, hu, hv, huv⟩ := G.exists_starX_ne C hC
  have h1 := hδ j u v huv
  have hu' := G.starX_mem_bounds hu j
  have hv' := G.starX_mem_bounds hv j
  have hw := C.bound_le_width j
  have : |G.starX j u - G.starX j v| ≤ C.hi j - C.lo j := by
    rw [abs_le]; constructor <;> linarith
  linarith

/-- lem:termination.  The construction terminates: there is no infinite sequence of cells,
each a child of the previous one under a step of def:construction, whatever good levels are
chosen. -/
theorem lem_termination (Rs : Fin k → List V) :
    WellFounded (fun C' C : Cell k => G.ConstrStep Rs C' C) := by
  obtain ⟨δ, hδ0, hδ⟩ := G.exists_delta
  have hθ0 : 0 < theta k := theta_pos
  have hθ1 : theta k < 1 := theta_lt_one
  let Φ : Cell k → ℕ := fun C => ∑ j : StarIdx k, levelIdx δ (1 - theta k) (C.hi j - C.lo j)
  have hstep : ∀ C' C, G.ConstrStep Rs C' C → Φ C' < Φ C := by
    rintro C' C ⟨j, lam, ⟨hC, hj, -, hlo, hhi, -⟩, hC'⟩
    have hwj : C.hi j - C.lo j = C.width := by rw [← C.ext_star j, hj]
    have hwδ := G.delta_le_of_not_atMostOneClass hδ C hC
    have hθw : 0 ≤ theta k * C.width := by nlinarith
    -- the cut coordinate drops
    have hdrop : levelIdx δ (1 - theta k) (C'.hi j - C'.lo j) <
        levelIdx δ (1 - theta k) (C.hi j - C.lo j) := by
      apply levelIdx_lt hδ0 (by linarith) (by linarith) (by linarith)
      rcases hC' with rfl | rfl
      · simp only [Cell.lower, Function.update_self]
        rw [max_eq_right (by linarith)]
        nlinarith
      · simp only [Cell.upper, Function.update_self]
        rw [min_eq_right (by linarith)]
        nlinarith
    -- the other coordinates are unchanged
    have hsame : ∀ j', j' ≠ j → C'.hi j' - C'.lo j' = C.hi j' - C.lo j' := by
      intro j' h
      rcases hC' with rfl | rfl
      · simp [Cell.lower, Function.update_of_ne h]
      · simp [Cell.upper, Function.update_of_ne h]
    apply Finset.sum_lt_sum
    · intro j' _
      by_cases h : j' = j
      · subst h; exact hdrop.le
      · rw [hsame j' h]
    · exact ⟨j, Finset.mem_univ _, hdrop⟩
  exact Subrelation.wf (fun {C' C} h => hstep C' C h) (InvImage.wf Φ wellFounded_lt)

/-- A cell whose vertex set meets two point classes has positive width (text of
def:construction). -/
theorem width_pos_of_not_atMostOneClass (C : Cell k)
    (hC : ¬ G.AtMostOneClass (G.cellVerts C)) : 0 < C.width := by
  obtain ⟨δ, hδ0, hδ⟩ := G.exists_delta
  exact lt_of_lt_of_le hδ0 (G.delta_le_of_not_atMostOneClass hδ C hC)

/-- A cell that is not a leaf of the construction can be cut: it has positive width and a good
level in a widest star coordinate (cor:goodlevel; text of def:construction). -/
theorem exists_constrCut (Rs : Fin k → List V) (hRs : ∀ l, G.IsDPath l (Rs l)) (C : Cell k)
    (hC : ¬ G.AtMostOneClass (G.cellVerts C)) :
    ∃ j lam, G.ConstrCut Rs C j lam := by
  obtain ⟨j0, -⟩ := G.exists_starX_ne C hC
  have : Nonempty (StarIdx k) := ⟨j0⟩
  obtain ⟨j, hj⟩ := exists_eq_ciSup_of_finite (f := fun j : StarIdx k => C.ext 0 j.1)
  have hj' : C.ext 0 j.1 = C.width := hj
  obtain ⟨lam, hlam⟩ :=
    G.cor_goodlevel Rs hRs C j (G.width_pos_of_not_atMostOneClass C hC) hj'
  exact ⟨j, lam, hC, hj', hlam⟩

/-- The tree of def:construction exists (and is finite) for every start cell. -/
theorem exists_constructionTree (Rs : Fin k → List V) (hRs : ∀ l, G.IsDPath l (Rs l))
    (C : Cell k) : ∃ T : CutTree k, G.IsConstructionTree Rs T C := by
  refine (G.lem_termination Rs).induction (C := fun D => ∃ T : CutTree k, G.IsConstructionTree Rs T D) C ?_
  intro C ih
  by_cases hC : G.AtMostOneClass (G.cellVerts C)
  · exact ⟨.leaf, hC⟩
  · obtain ⟨j, lam, hcut⟩ := G.exists_constrCut Rs hRs C hC
    obtain ⟨lt, hlt⟩ := ih _ ⟨j, lam, hcut, Or.inl rfl⟩
    obtain ⟨rt, hrt⟩ := ih _ ⟨j, lam, hcut, Or.inr rfl⟩
    exact ⟨.node j lam lt rt, hcut, hlt, hrt⟩

/-- A construction tree is a hierarchy: since `θ > 0`, every chosen level lies strictly between
the bounds (text after def:construction). -/
theorem isHierarchy_of_isConstructionTree (Rs : Fin k → List V) (T : CutTree k) (C : Cell k)
    (h : G.IsConstructionTree Rs T C) : G.IsHierarchy T C := by
  induction T generalizing C with
  | leaf => trivial
  | node j lam lt rt ihl ihr =>
    obtain ⟨⟨hC, -, hg, hlo, hhi, -⟩, hl, hr⟩ := h
    have hθ : (0 : ℝ) < theta k := by
      unfold theta
      have : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne k)
      positivity
    have hw : 0 < C.width := G.width_pos_of_not_atMostOneClass C hC
    exact ⟨hg, by nlinarith, by nlinarith, ihl _ hl, ihr _ hr⟩

end Instance

end DSPP
