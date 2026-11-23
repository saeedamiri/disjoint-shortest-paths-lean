/-
Closure of the table recursion (def:table) under taking children.

Paper: "Directed k Disjoint Shortest Paths Is Polynomial for Every Fixed k" (Saeed Amiri),
Section "The algorithm", subsections "The table" and "Running time".
-/
import DSPP.Table
import DSPP.Complexity

open Classical

namespace DSPP

variable {k : ℕ} [NeZero k] {V : Type*} [Fintype V] [DecidableEq V]

namespace Instance

variable (G : Instance V k)

theorem isBoxSet_Uminus {U : Finset V} (hU : G.IsBoxSet U) {sp : StarIdx k × ℝ × ℝ}
    (hsp : sp ∈ G.splits U) : G.IsBoxSet (G.Uminus U sp) := by
  obtain ⟨hne, α, β, hab, rfl⟩ := hU
  obtain ⟨hmem, -, -, -⟩ := G.isSplit_of_mem_splits hsp
  obtain ⟨w, hw, hwx⟩ := Finset.mem_image.1 hmem
  have hw' := (G.mem_boxOf).1 hw
  refine ⟨⟨w, ?_⟩, α, Function.update β sp.1 sp.2.1, ?_, ?_⟩
  · simp [Uminus, hw, hwx]
  · intro j
    by_cases hj : j = sp.1
    · subst hj
      exact ⟨(hab _).1, by simpa using hwx ▸ G.starX_mem_Lam _ w⟩
    · simpa [Function.update_of_ne hj] using (hab j).2 |> fun h => And.intro (hab j).1 h
  · ext v
    simp only [Uminus, Finset.mem_filter, G.mem_boxOf]
    constructor
    · rintro ⟨hv, hle⟩ j
      by_cases hj : j = sp.1
      · subst hj; simpa using ⟨(hv _).1, hle⟩
      · simpa [Function.update_of_ne hj] using hv j
    · intro h
      refine ⟨fun j => ⟨(h j).1, ?_⟩, ?_⟩
      · by_cases hj : j = sp.1
        · subst hj
          have h1 := (h sp.1).2
          simp only [Function.update_self] at h1
          exact h1.trans (hwx ▸ (hw' sp.1).2)
        · simpa [Function.update_of_ne hj] using (h j).2
      · have h2 := (h sp.1).2
        simpa using h2

theorem isBoxSet_Uplus {U : Finset V} (hU : G.IsBoxSet U) {sp : StarIdx k × ℝ × ℝ}
    (hsp : sp ∈ G.splits U) : G.IsBoxSet (G.Uplus U sp) := by
  obtain ⟨hne, α, β, hab, rfl⟩ := hU
  obtain ⟨-, hmem, -, -⟩ := G.isSplit_of_mem_splits hsp
  obtain ⟨w, hw, hwx⟩ := Finset.mem_image.1 hmem
  have hw' := (G.mem_boxOf).1 hw
  refine ⟨⟨w, ?_⟩, Function.update α sp.1 sp.2.2, β, ?_, ?_⟩
  · simp [Uplus, hw, hwx]
  · intro j
    by_cases hj : j = sp.1
    · subst hj
      exact ⟨by simpa using hwx ▸ G.starX_mem_Lam _ w, (hab _).2⟩
    · simpa [Function.update_of_ne hj] using And.intro (hab j).1 (hab j).2
  · ext v
    simp only [Uplus, Finset.mem_filter, G.mem_boxOf]
    constructor
    · rintro ⟨hv, hle⟩ j
      by_cases hj : j = sp.1
      · subst hj; simpa using ⟨hle, (hv _).2⟩
      · simpa [Function.update_of_ne hj] using hv j
    · intro h
      refine ⟨fun j => ⟨?_, (h j).2⟩, ?_⟩
      · by_cases hj : j = sp.1
        · subst hj
          have h1 := (h sp.1).1
          simp only [Function.update_self] at h1
          exact (hwx ▸ (hw' sp.1).1).trans h1
        · simpa [Function.update_of_ne hj] using (h j).1
      · have h2 := (h sp.1).1
        simpa using h2

theorem not_mem_Uplus_of_mem_Uminus {U : Finset V} {sp : StarIdx k × ℝ × ℝ}
    (hsp : sp ∈ G.splits U) {v : V} (hv : v ∈ G.Uminus U sp) : v ∉ G.Uplus U sp := by
  obtain ⟨-, -, hlt, -⟩ := G.isSplit_of_mem_splits hsp
  intro h
  have h1 := (Finset.mem_filter.1 hv).2
  have h2 := (Finset.mem_filter.1 h).2
  exact absurd (h2.trans h1) (not_le.2 hlt)

/-- The recursion of def:table from an entry visits only entries: the two children of an entry
along a split and a valid interface are entries.  Hence lem:time, which counts the work over
entries, bounds the work of evaluating the root. -/
theorem isEntry_children {U : Finset V} {Dm : Finset (Demand V k)} (hE : G.IsEntry U Dm)
    {sp : StarIdx k × ℝ × ℝ} (hsp : sp ∈ G.splits U) {I : Finset (ArcDemand V k)}
    (_hI : I ∈ G.interfaces U Dm sp) (hV : G.Valid U Dm sp I) :
    G.IsEntry (G.Uminus U sp) (G.PiMinus U Dm sp I) ∧
      G.IsEntry (G.Uplus U sp) (G.PiPlus U Dm sp I) := by
  obtain ⟨hU, -, -⟩ := hE
  have hU' : G.IsBoxSet U := (Finset.mem_filter.1 hU).2
  obtain ⟨-, hv1, -, hv3m, hv3p⟩ := hV
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, G.isBoxSet_Uminus hU' hsp⟩
  · exact Multiset.toFinset_card_le _ |>.trans hv3m
  · intro δ hδ
    obtain ⟨hδ, hm⟩ := Multiset.mem_filter.1 (Multiset.mem_toFinset.1 hδ)
    rcases hv1 δ hδ with h | h
    · exact h
    · exact absurd h.1 (G.not_mem_Uplus_of_mem_Uminus hsp hm)
  · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, G.isBoxSet_Uplus hU' hsp⟩
  · exact Multiset.toFinset_card_le _ |>.trans hv3p
  · intro δ hδ
    obtain ⟨hδ, hm⟩ := Multiset.mem_filter.1 (Multiset.mem_toFinset.1 hδ)
    rcases hv1 δ hδ with h | h
    · exact absurd hm (G.not_mem_Uplus_of_mem_Uminus hsp h.1)
    · exact h

end Instance

end DSPP
