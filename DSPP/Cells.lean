/-
Cells, extents, width; lem:extent.

Paper: "Directed k Disjoint Shortest Paths Is Polynomial for Every Fixed k" (Saeed Amiri),
Section "Preliminaries", subsection "Cells" (def:cell, lem:extent).
-/
import DSPP.Potentials

open Classical

namespace DSPP

variable {k : ℕ} [NeZero k]

/-- def:cell.  A cell is given by real bounds `a_j ≤ b_j` on the star coordinates
`X_{1j}`, `j = 2, ..., k`. -/
structure Cell (k : ℕ) [NeZero k] where
  /-- Lower bounds `a_j`. -/
  lo : StarIdx k → ℝ
  /-- Upper bounds `b_j`. -/
  hi : StarIdx k → ℝ
  /-- `a_j ≤ b_j`. -/
  lo_le_hi : ∀ j, lo j ≤ hi j

namespace Cell

/-- The point set `C = {x ∈ ℝ^k : a_j ≤ X_{1j}(x) ≤ b_j for all j}`. -/
def carrier (C : Cell k) : Set (Fin k → ℝ) :=
  {x | ∀ j : StarIdx k, C.lo j ≤ X 0 j.1 x ∧ X 0 j.1 x ≤ C.hi j}

/-- The extent `ext_{ij}(C) = max_C X_{ij} - min_C X_{ij}`. -/
noncomputable def ext (C : Cell k) (i j : Fin k) : ℝ :=
  sSup (X i j '' C.carrier) - sInf (X i j '' C.carrier)

/-- The width `w(C) = max_{2 ≤ j ≤ k} ext_{1j}(C)`. -/
noncomputable def width (C : Cell k) : ℝ := ⨆ j : StarIdx k, C.ext 0 j.1

/-- The child `C ∩ {X_{1j} ≤ λ}` of a cut at `(1,j,λ)`: the upper bound in `X_{1j}` is replaced
by `λ` (clamped from below by `a_j` so that the bounds stay valid; in a hierarchy
`a_j < λ < b_j`, and then this is exactly the cell of lem:extent (c)). -/
noncomputable def lower (C : Cell k) (j : StarIdx k) (lam : ℝ) : Cell k where
  lo := C.lo
  hi := Function.update C.hi j (max (C.lo j) lam)
  lo_le_hi := by
    intro j'
    by_cases h : j' = j
    · subst h; simp
    · simp [Function.update_of_ne h, C.lo_le_hi j']

/-- The child `C ∩ {X_{1j} ≥ λ}` of a cut at `(1,j,λ)`: the lower bound in `X_{1j}` is replaced
by `λ` (clamped from above by `b_j`). -/
noncomputable def upper (C : Cell k) (j : StarIdx k) (lam : ℝ) : Cell k where
  lo := Function.update C.lo j (min (C.hi j) lam)
  hi := C.hi
  lo_le_hi := by
    intro j'
    by_cases h : j' = j
    · subst h; simp
    · simp [Function.update_of_ne h, C.lo_le_hi j']

/-- A vector on `Fin k` from star coordinates, with the value `0` at index `0`. -/
noncomputable def ext0 (y : StarIdx k → ℝ) (m : Fin k) : ℝ :=
  if h : m = 0 then 0 else y ⟨m, h⟩

theorem exists_witness (C : Cell k) (y : StarIdx k → ℝ)
    (hy : ∀ j, y j ∈ Set.Icc (C.lo j) (C.hi j)) :
    ∃ x ∈ C.carrier, ∀ m, X 0 m x = ext0 y m := by
  refine ⟨fun m => -ext0 y m, ?_, ?_⟩
  · intro j
    have : X 0 j.1 (fun m => -ext0 y m) = y j := by simp [X, ext0, j.2]
    rw [this]; exact hy j
  · intro m; simp [X, ext0]

theorem bounds_of_mem (C : Cell k) {x : Fin k → ℝ} (hx : x ∈ C.carrier) (m : Fin k) :
    ext0 C.lo m ≤ X 0 m x ∧ X 0 m x ≤ ext0 C.hi m := by
  by_cases h : m = 0
  · subst h; simp [ext0, X]
  · simp only [ext0, dif_neg h]; exact hx ⟨m, h⟩

theorem extreme (C : Cell k) {i j : Fin k} (hij : i ≠ j) :
    IsGreatest (X i j '' C.carrier) (ext0 C.hi j - ext0 C.lo i) ∧
    IsLeast (X i j '' C.carrier) (ext0 C.lo j - ext0 C.hi i) := by
  have hX : ∀ x : Fin k → ℝ, X i j x = X 0 j x - X 0 i x := by intro x; simp only [X]; ring
  constructor
  · obtain ⟨x, hx, hxy⟩ := exists_witness C (fun m => if m.1 = j then C.hi m else C.lo m)
      (fun m => by
        by_cases h : m.1 = j <;> simp [h, C.lo_le_hi m])
    refine ⟨⟨x, hx, ?_⟩, ?_⟩
    · rw [hX, hxy, hxy]
      have e1 : ext0 (fun m : StarIdx k => if m.1 = j then C.hi m else C.lo m) j =
          ext0 C.hi j := by
        by_cases h : j = 0
        · simp [ext0, h]
        · simp [ext0, h]
      have e2 : ext0 (fun m : StarIdx k => if m.1 = j then C.hi m else C.lo m) i =
          ext0 C.lo i := by
        by_cases h : i = 0
        · simp [ext0, h]
        · simp [ext0, h, hij]
      rw [e1, e2]
    · rintro _ ⟨x, hx, rfl⟩
      rw [hX]
      linarith [(bounds_of_mem C hx j).2, (bounds_of_mem C hx i).1]
  · obtain ⟨x, hx, hxy⟩ := exists_witness C (fun m => if m.1 = i then C.hi m else C.lo m)
      (fun m => by
        by_cases h : m.1 = i <;> simp [h, C.lo_le_hi m])
    refine ⟨⟨x, hx, ?_⟩, ?_⟩
    · rw [hX, hxy, hxy]
      have e1 : ext0 (fun m : StarIdx k => if m.1 = i then C.hi m else C.lo m) j =
          ext0 C.lo j := by
        by_cases h : j = 0
        · simp [ext0, h]
        · simp [ext0, h, hij.symm]
      have e2 : ext0 (fun m : StarIdx k => if m.1 = i then C.hi m else C.lo m) i =
          ext0 C.hi i := by
        by_cases h : i = 0
        · simp [ext0, h]
        · simp [ext0, h]
      rw [e1, e2]
    · rintro _ ⟨x, hx, rfl⟩
      rw [hX]
      linarith [(bounds_of_mem C hx j).1, (bounds_of_mem C hx i).2]

theorem ext_eq (C : Cell k) {i j : Fin k} (hij : i ≠ j) :
    C.ext i j = (ext0 C.hi i - ext0 C.lo i) + (ext0 C.hi j - ext0 C.lo j) := by
  obtain ⟨h1, h2⟩ := extreme C hij
  unfold ext
  rw [h1.csSup_eq, h2.csInf_eq]
  ring

theorem ext_self (C : Cell k) (i : Fin k) : C.ext i i = 0 := by
  unfold ext
  have hsub : X i i '' C.carrier ⊆ {0} := by
    rintro _ ⟨x, _, rfl⟩; simp [X]
  rcases C.carrier.eq_empty_or_nonempty with h | h
  · simp [h]
  · have : X i i '' C.carrier = {0} := by
      apply Set.Subset.antisymm hsub
      obtain ⟨x, hx⟩ := h
      intro z hz; rw [Set.mem_singleton_iff] at hz; subst hz
      exact ⟨x, hx, by simp [X]⟩
    rw [this]; simp

/-- lem:extent (a).  The star map sends `C` onto the box `∏ [a_j, b_j]`; `C` is non-empty,
closed, convex and invariant under adding multiples of `𝟙`. -/
theorem lem_extent_a (C : Cell k) :
    (fun x : Fin k → ℝ => fun j : StarIdx k => X 0 j.1 x) '' C.carrier =
        Set.pi Set.univ (fun j => Set.Icc (C.lo j) (C.hi j)) ∧
      C.carrier.Nonempty ∧ IsClosed C.carrier ∧ Convex ℝ C.carrier ∧
      ∀ x ∈ C.carrier, ∀ c : ℝ, x + c • one k ∈ C.carrier := by
  have himg : (fun x : Fin k → ℝ => fun j : StarIdx k => X 0 j.1 x) '' C.carrier =
      Set.pi Set.univ (fun j => Set.Icc (C.lo j) (C.hi j)) := by
    apply Set.Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      rw [Set.mem_pi]
      intro j _
      exact hx j
    · intro y hy
      rw [Set.mem_pi] at hy
      obtain ⟨x, hx, h⟩ := exists_witness C y (fun j => hy j (Set.mem_univ _))
      refine ⟨x, hx, funext fun j => ?_⟩
      simp [h, ext0, j.2]
  have hne : C.carrier.Nonempty := by
    obtain ⟨x, hx, _⟩ := exists_witness C C.lo (fun j => ⟨le_rfl, C.lo_le_hi j⟩)
    exact ⟨x, hx⟩
  refine ⟨himg, hne, ?_, ?_, ?_⟩
  · have : C.carrier = ⋂ j : StarIdx k,
        ({x | C.lo j ≤ X 0 j.1 x} ∩ {x | X 0 j.1 x ≤ C.hi j}) := by
      ext x; simp [carrier]
    rw [this]
    refine isClosed_iInter fun j => IsClosed.inter ?_ ?_
    · exact isClosed_le continuous_const (by unfold X; fun_prop)
    · exact isClosed_le (by unfold X; fun_prop) continuous_const
  · intro x hx y hy a b ha hb hab j
    obtain ⟨h1, h2⟩ := hx j
    obtain ⟨h3, h4⟩ := hy j
    have e : X 0 j.1 (a • x + b • y) = a * X 0 j.1 x + b * X 0 j.1 y := by
      simp only [X, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [e]
    have m1 := mul_le_mul_of_nonneg_left h1 ha
    have m2 := mul_le_mul_of_nonneg_left h3 hb
    have m3 := mul_le_mul_of_nonneg_left h2 ha
    have m4 := mul_le_mul_of_nonneg_left h4 hb
    have e1 : a * C.lo j + b * C.lo j = C.lo j := by rw [← add_mul, hab, one_mul]
    have e2 : a * C.hi j + b * C.hi j = C.hi j := by rw [← add_mul, hab, one_mul]
    constructor <;> linarith
  · intro x hx c j
    have e : X 0 j.1 (x + c • one k) = X 0 j.1 x := by
      simp [X, one]
    rw [e]; exact hx j

/-- lem:extent (b).  `ext_{1j}(C) = E_j`, `ext_{ij}(C) = E_i + E_j` for star indices `i ≠ j`,
`w(C) = max_j E_j`, every extent is at most `2 w(C)`, and the bounds are the extreme values of
`X_{1j}` on `C`. -/
theorem lem_extent_b (C : Cell k) :
    (∀ j : StarIdx k, C.ext 0 j.1 = C.hi j - C.lo j) ∧
    (∀ i j : StarIdx k, i ≠ j → C.ext i.1 j.1 = (C.hi i - C.lo i) + (C.hi j - C.lo j)) ∧
    (∀ i j : Fin k, C.ext i j = C.ext j i) ∧
    C.width = ⨆ j : StarIdx k, (C.hi j - C.lo j) ∧
    (∀ i j : Fin k, C.ext i j ≤ 2 * C.width) ∧
    (∀ j : StarIdx k, IsLeast (X 0 j.1 '' C.carrier) (C.lo j) ∧
      IsGreatest (X 0 j.1 '' C.carrier) (C.hi j)) := by
  have h0 : ∀ j : StarIdx k, (0 : Fin k) ≠ j.1 := fun j => j.2.symm
  have e0 : ext0 C.hi 0 = 0 := by simp [ext0]
  have e0' : ext0 C.lo 0 = 0 := by simp [ext0]
  have eS : ∀ (f : StarIdx k → ℝ) (j : StarIdx k), ext0 f j.1 = f j := by
    intro f j; simp [ext0, j.2]
  have hE : ∀ j : StarIdx k, C.ext 0 j.1 = C.hi j - C.lo j := by
    intro j
    rw [ext_eq C (h0 j), e0, e0', eS, eS]; ring
  have hW : C.width = ⨆ j : StarIdx k, (C.hi j - C.lo j) := by
    unfold width; congr 1; ext j; exact hE j
  have hwnn : 0 ≤ C.width := by
    rw [hW]
    exact Real.iSup_nonneg fun j => sub_nonneg.mpr (C.lo_le_hi j)
  have hle : ∀ j : StarIdx k, C.hi j - C.lo j ≤ C.width := by
    intro j
    rw [hW]
    exact le_ciSup (f := fun j : StarIdx k => C.hi j - C.lo j) (Set.finite_range _).bddAbove j
  have hEm : ∀ m : Fin k, ext0 C.hi m - ext0 C.lo m ≤ C.width := by
    intro m
    by_cases h : m = 0
    · subst h; simp [ext0, hwnn]
    · have := hle ⟨m, h⟩
      simpa [ext0, h] using this
  refine ⟨hE, ?_, ?_, hW, ?_, ?_⟩
  · intro i j hij
    rw [ext_eq C (fun h => hij (Subtype.ext h)), eS, eS, eS, eS]
  · intro i j
    by_cases h : i = j
    · subst h; rfl
    · rw [ext_eq C h, ext_eq C (Ne.symm h)]; ring
  · intro i j
    by_cases h : i = j
    · subst h; rw [ext_self]; linarith
    · rw [ext_eq C h]; linarith [hEm i, hEm j]
  · intro j
    obtain ⟨h1, h2⟩ := extreme C (h0 j)
    rw [e0', eS, sub_zero] at h1
    rw [e0, eS, sub_zero] at h2
    exact ⟨h2, h1⟩

/-- lem:extent (c).  Cutting a cell by a half-space of a star coordinate gives the cell with
one bound replaced, or the empty set. -/
theorem lem_extent_c (C : Cell k) (j : StarIdx k) (lam : ℝ) :
    (C.lo j ≤ lam → C.carrier ∩ {x | X 0 j.1 x ≤ lam} = (C.lower j (min (C.hi j) lam)).carrier) ∧
    (lam < C.lo j → C.carrier ∩ {x | X 0 j.1 x ≤ lam} = ∅) ∧
    (lam ≤ C.hi j → C.carrier ∩ {x | lam ≤ X 0 j.1 x} = (C.upper j (max (C.lo j) lam)).carrier) ∧
    (C.hi j < lam → C.carrier ∩ {x | lam ≤ X 0 j.1 x} = ∅) := by
  refine ⟨fun hl => ?_, fun hl => ?_, fun hu => ?_, fun hu => ?_⟩
  · have hmax : max (C.lo j) (min (C.hi j) lam) = min (C.hi j) lam :=
      max_eq_right (le_min (C.lo_le_hi j) hl)
    ext x
    constructor
    · rintro ⟨hx, hxl⟩ m
      refine ⟨(hx m).1, ?_⟩
      by_cases hm : m = j
      · subst hm
        simp only [lower, Function.update_self, hmax]
        exact le_min (hx m).2 hxl
      · simp only [lower, Function.update_of_ne hm]
        exact (hx m).2
    · intro hx
      have hx' : ∀ m, C.lo m ≤ X 0 m.1 x ∧ X 0 m.1 x ≤ (C.lower j (min (C.hi j) lam)).hi m := hx
      refine ⟨fun m => ⟨(hx' m).1, ?_⟩, ?_⟩
      · by_cases hm : m = j
        · subst hm
          have := (hx' m).2
          simp only [lower, Function.update_self, hmax] at this
          exact this.trans (min_le_left _ _)
        · have := (hx' m).2
          simp only [lower, Function.update_of_ne hm] at this
          exact this
      · have := (hx' j).2
        simp only [lower, Function.update_self, hmax] at this
        exact this.trans (min_le_right _ _)
  · ext x
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    intro hx hxl
    have hxl : X 0 j.1 x ≤ lam := hxl
    have := (hx j).1
    linarith
  · have hmax : min (C.hi j) (max (C.lo j) lam) = max (C.lo j) lam :=
      min_eq_right (max_le (C.lo_le_hi j) hu)
    ext x
    constructor
    · rintro ⟨hx, hxl⟩ m
      refine ⟨?_, (hx m).2⟩
      by_cases hm : m = j
      · subst hm
        simp only [upper, Function.update_self, hmax]
        exact max_le (hx m).1 hxl
      · simp only [upper, Function.update_of_ne hm]
        exact (hx m).1
    · intro hx
      have hx' : ∀ m, (C.upper j (max (C.lo j) lam)).lo m ≤ X 0 m.1 x ∧ X 0 m.1 x ≤ C.hi m := hx
      refine ⟨fun m => ⟨?_, (hx' m).2⟩, ?_⟩
      · by_cases hm : m = j
        · subst hm
          have := (hx' m).1
          simp only [upper, Function.update_self, hmax] at this
          exact (le_max_left _ _).trans this
        · have := (hx' m).1
          simp only [upper, Function.update_of_ne hm] at this
          exact this
      · have := (hx' j).1
        simp only [upper, Function.update_self, hmax] at this
        exact (le_max_right _ _).trans this
  · ext x
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    intro hx hxl
    have hxl : lam ≤ X 0 j.1 x := hxl
    have := (hx j).2
    linarith

end Cell

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace Instance

variable (G : Instance V k)

/-- The value of the star coordinate `X_{1j}` at a vertex. -/
noncomputable def starX (j : StarIdx k) (v : V) : ℝ := G.Xv 0 j.1 v

/-- `V(C) = {v ∈ V : π(v) ∈ C}`. -/
noncomputable def cellVerts (C : Cell k) : Finset V :=
  Finset.univ.filter fun v => G.pt v ∈ C.carrier

end Instance

end DSPP
