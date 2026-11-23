/-
Box sets (def:box, lem:box) and point classes as vertex sets.

Paper: "Directed k Disjoint Shortest Paths Is Polynomial for Every Fixed k" (Saeed Amiri),
Section "The algorithm", subsection "Box sets".
-/
import DSPP.Hierarchy

open Classical

namespace DSPP

variable {k : ℕ} [NeZero k] {V : Type*} [Fintype V] [DecidableEq V]

namespace Instance

variable (G : Instance V k)

/-- `Λ_j = {X_{1j}(v) : v ∈ V}`. -/
noncomputable def Lam (j : StarIdx k) : Finset ℝ := Finset.univ.image (G.starX j)

/-- The vertices with `α_j ≤ X_{1j}(v) ≤ β_j` for all star indices `j`. -/
noncomputable def boxOf (α β : StarIdx k → ℝ) : Finset V :=
  Finset.univ.filter fun v => ∀ j, α j ≤ G.starX j v ∧ G.starX j v ≤ β j

/-- def:box.  A box set: a non-empty set `{v : α_j ≤ X_{1j}(v) ≤ β_j}` with `α_j, β_j ∈ Λ_j`. -/
def IsBoxSet (U : Finset V) : Prop :=
  U.Nonempty ∧ ∃ α β : StarIdx k → ℝ, (∀ j, α j ∈ G.Lam j ∧ β j ∈ G.Lam j) ∧ U = G.boxOf α β

/-- def:box.  The family `𝒰` of box sets. -/
noncomputable def boxSets : Finset (Finset V) := Finset.univ.filter G.IsBoxSet

/-- The point class of `v`, as a set of vertices. -/
noncomputable def pointClass (v : V) : Finset V := Finset.univ.filter (G.SameClass v)

/-- `U` is a point class. -/
def IsPointClass (U : Finset V) : Prop := ∃ v, U = G.pointClass v

theorem mem_boxOf {α β : StarIdx k → ℝ} {v : V} :
    v ∈ G.boxOf α β ↔ ∀ j, α j ≤ G.starX j v ∧ G.starX j v ≤ β j := by
  simp [boxOf]

theorem starX_mem_Lam (j : StarIdx k) (v : V) : G.starX j v ∈ G.Lam j := by
  simp [Lam]

theorem starX_eq_of_sameClass {u v : V} (h : G.SameClass u v) (j : StarIdx k) :
    G.starX j u = G.starX j v := h 0 j.1

theorem card_starIdx : Fintype.card (StarIdx k) = k - 1 := by
  rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_subtype_eq]

/-- lem:box (a).  `|𝒰| ≤ n^{2(k-1)}`, and `V ∈ 𝒰`. -/
theorem lem_box_a :
    G.boxSets.card ≤ Fintype.card V ^ (2 * (k - 1)) ∧ Finset.univ ∈ G.boxSets := by
  have hV : Nonempty V := ⟨G.s 0⟩
  constructor
  · let T : Finset ((StarIdx k → ℝ) × (StarIdx k → ℝ)) :=
      Fintype.piFinset (fun j => G.Lam j) ×ˢ Fintype.piFinset (fun j => G.Lam j)
    have hsub : G.boxSets ⊆ T.image (fun p => G.boxOf p.1 p.2) := by
      intro U hU
      rw [boxSets, Finset.mem_filter] at hU
      obtain ⟨_, _, α, β, hab, rfl⟩ := hU
      rw [Finset.mem_image]
      refine ⟨(α, β), ?_, rfl⟩
      simp only [T, Finset.mem_product, Fintype.mem_piFinset]
      exact ⟨fun j => (hab j).1, fun j => (hab j).2⟩
    have hcard : ∀ j : StarIdx k, (G.Lam j).card ≤ Fintype.card V := by
      intro j
      exact Finset.card_image_le.trans (by simp)
    have hprod : ∏ j : StarIdx k, (G.Lam j).card ≤ Fintype.card V ^ (k - 1) := by
      have := Finset.prod_le_pow_card (Finset.univ : Finset (StarIdx k))
        (fun j => (G.Lam j).card) (Fintype.card V) (fun j _ => hcard j)
      rwa [Finset.card_univ, card_starIdx] at this
    calc G.boxSets.card ≤ (T.image (fun p => G.boxOf p.1 p.2)).card := Finset.card_le_card hsub
      _ ≤ T.card := Finset.card_image_le
      _ = (∏ j : StarIdx k, (G.Lam j).card) * (∏ j : StarIdx k, (G.Lam j).card) := by
        simp only [T, Finset.card_product, Fintype.card_piFinset]
      _ ≤ Fintype.card V ^ (k - 1) * Fintype.card V ^ (k - 1) := Nat.mul_le_mul hprod hprod
      _ = Fintype.card V ^ (2 * (k - 1)) := by rw [← pow_add]; ring_nf
  · have hne : ∀ j : StarIdx k, (G.Lam j).Nonempty := fun j =>
      ⟨_, G.starX_mem_Lam j (Classical.choice hV)⟩
    rw [boxSets, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, Finset.univ_nonempty, fun j => (G.Lam j).min' (hne j),
      fun j => (G.Lam j).max' (hne j), fun j => ⟨Finset.min'_mem _ _, Finset.max'_mem _ _⟩, ?_⟩
    ext v
    simp only [Finset.mem_univ, true_iff, mem_boxOf]
    intro j
    exact ⟨Finset.min'_le _ _ (G.starX_mem_Lam j v), Finset.le_max' _ _ (G.starX_mem_Lam j v)⟩

/-- lem:box (b).  A box set is the box set of its tight bounds. -/
theorem lem_box_b {U : Finset V} (hU : G.IsBoxSet U) (α β : StarIdx k → ℝ)
    (hα : ∀ j, IsLeast (G.starX j '' U) (α j)) (hβ : ∀ j, IsGreatest (G.starX j '' U) (β j)) :
    U = G.boxOf α β := by
  obtain ⟨_, α', β', _, hU'⟩ := hU
  ext v
  rw [mem_boxOf]
  constructor
  · intro hv j
    exact ⟨(hα j).2 ⟨v, hv, rfl⟩, (hβ j).2 ⟨v, hv, rfl⟩⟩
  · intro hv
    rw [hU', mem_boxOf]
    intro j
    obtain ⟨a, ha, hae⟩ := (hα j).1
    obtain ⟨b, hb, hbe⟩ := (hβ j).1
    have ha' : a ∈ G.boxOf α' β' := by rw [← hU']; exact ha
    have hb' : b ∈ G.boxOf α' β' := by rw [← hU']; exact hb
    rw [mem_boxOf] at ha' hb'
    refine ⟨?_, ?_⟩
    · have := (ha' j).1
      rw [hae] at this
      exact this.trans (hv j).1
    · have := (hb' j).2
      rw [hbe] at this
      exact (hv j).2.trans this

/-- lem:box (c).  If `V(C) ≠ ∅` for a cell `C`, then `V(C)` is a box set. -/
theorem lem_box_c (C : Cell k) (hC : (G.cellVerts C).Nonempty) : G.IsBoxSet (G.cellVerts C) := by
  have hmem : ∀ v, v ∈ G.cellVerts C ↔ ∀ j, C.lo j ≤ G.starX j v ∧ G.starX j v ≤ C.hi j := by
    intro v
    simp only [cellVerts, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Iff.rfl
  have hne : ∀ j : StarIdx k, ((G.cellVerts C).image (G.starX j)).Nonempty := fun j =>
    hC.image _
  refine ⟨hC, fun j => ((G.cellVerts C).image (G.starX j)).min' (hne j),
    fun j => ((G.cellVerts C).image (G.starX j)).max' (hne j), ?_, ?_⟩
  · intro j
    show ((G.cellVerts C).image (G.starX j)).min' (hne j) ∈ G.Lam j ∧
      ((G.cellVerts C).image (G.starX j)).max' (hne j) ∈ G.Lam j
    have h1 := Finset.min'_mem _ (hne j)
    have h2 := Finset.max'_mem _ (hne j)
    rw [Finset.mem_image] at h1 h2
    obtain ⟨a, _, ha⟩ := h1
    obtain ⟨b, _, hb⟩ := h2
    exact ⟨by rw [← ha]; exact G.starX_mem_Lam j a, by rw [← hb]; exact G.starX_mem_Lam j b⟩
  · ext v
    rw [mem_boxOf]
    constructor
    · intro hv j
      exact ⟨Finset.min'_le _ _ (Finset.mem_image_of_mem _ hv),
        Finset.le_max' _ _ (Finset.mem_image_of_mem _ hv)⟩
    · intro hv
      rw [hmem]
      intro j
      have h1 := Finset.min'_mem _ (hne j)
      have h2 := Finset.max'_mem _ (hne j)
      rw [Finset.mem_image] at h1 h2
      obtain ⟨a, ha, hae⟩ := h1
      obtain ⟨b, hb, hbe⟩ := h2
      rw [hmem] at ha hb
      refine ⟨?_, ?_⟩
      · have := (ha j).1
        rw [hae] at this
        exact this.trans (hv j).1
      · have := (hb j).2
        rw [hbe] at this
        exact (hv j).2.trans this

/-- lem:box (d).  Cutting a box set at a value of `Λ_j` gives box sets (when non-empty). -/
theorem lem_box_d {U : Finset V} (hU : G.IsBoxSet U) (j : StarIdx k) {α : ℝ}
    (hα : α ∈ G.Lam j) :
    ((U.filter fun v => G.starX j v ≤ α).Nonempty →
        G.IsBoxSet (U.filter fun v => G.starX j v ≤ α)) ∧
      ((U.filter fun v => α ≤ G.starX j v).Nonempty →
        G.IsBoxSet (U.filter fun v => α ≤ G.starX j v)) := by
  obtain ⟨_, a, b, hab, hU'⟩ := hU
  constructor
  · intro hne
    refine ⟨hne, a, Function.update b j (min (b j) α), ?_, ?_⟩
    · intro m
      refine ⟨(hab m).1, ?_⟩
      by_cases hm : m = j
      · subst hm
        rw [Function.update_self]
        rcases min_choice (b m) α with h | h <;> rw [h]
        · exact (hab m).2
        · exact hα
      · rw [Function.update_of_ne hm]; exact (hab m).2
    · ext v
      rw [Finset.mem_filter, hU', mem_boxOf, mem_boxOf]
      constructor
      · rintro ⟨hv, hvα⟩ m
        refine ⟨(hv m).1, ?_⟩
        by_cases hm : m = j
        · subst hm
          rw [Function.update_self]
          exact le_min (hv m).2 hvα
        · rw [Function.update_of_ne hm]; exact (hv m).2
      · intro hv
        refine ⟨fun m => ⟨(hv m).1, ?_⟩, ?_⟩
        · by_cases hm : m = j
          · subst hm
            have := (hv m).2
            rw [Function.update_self] at this
            exact this.trans (min_le_left _ _)
          · have := (hv m).2
            rw [Function.update_of_ne hm] at this
            exact this
        · have := (hv j).2
          rw [Function.update_self] at this
          exact this.trans (min_le_right _ _)
  · intro hne
    refine ⟨hne, Function.update a j (max (a j) α), b, ?_, ?_⟩
    · intro m
      refine ⟨?_, (hab m).2⟩
      by_cases hm : m = j
      · subst hm
        rw [Function.update_self]
        rcases max_choice (a m) α with h | h <;> rw [h]
        · exact (hab m).1
        · exact hα
      · rw [Function.update_of_ne hm]; exact (hab m).1
    · ext v
      rw [Finset.mem_filter, hU', mem_boxOf, mem_boxOf]
      constructor
      · rintro ⟨hv, hvα⟩ m
        refine ⟨?_, (hv m).2⟩
        by_cases hm : m = j
        · subst hm
          rw [Function.update_self]
          exact max_le (hv m).1 hvα
        · rw [Function.update_of_ne hm]; exact (hv m).1
      · intro hv
        refine ⟨fun m => ⟨?_, (hv m).2⟩, ?_⟩
        · by_cases hm : m = j
          · subst hm
            have := (hv m).1
            rw [Function.update_self] at this
            exact (le_max_left _ _).trans this
          · have := (hv m).1
            rw [Function.update_of_ne hm] at this
            exact this
        · have := (hv j).1
          rw [Function.update_self] at this
          exact (le_max_right _ _).trans this

/-- lem:box (e).  Every box set is a union of point classes, and a box set that meets only one
point class is that point class. -/
theorem lem_box_e {U : Finset V} (hU : G.IsBoxSet U) :
    (∀ u ∈ U, ∀ v, G.SameClass u v → v ∈ U) ∧ (G.AtMostOneClass U → G.IsPointClass U) := by
  have h1 : ∀ u ∈ U, ∀ v, G.SameClass u v → v ∈ U := by
    obtain ⟨_, α, β, _, hU'⟩ := hU
    intro u hu v huv
    rw [hU', mem_boxOf] at hu ⊢
    intro j
    rw [← G.starX_eq_of_sameClass huv j]
    exact hu j
  refine ⟨h1, fun hone => ?_⟩
  obtain ⟨v, hv⟩ := hU.1
  refine ⟨v, ?_⟩
  ext u
  simp only [pointClass, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun hu => hone v hv u hu, fun hu => h1 v hv u hu⟩

end Instance

end DSPP
