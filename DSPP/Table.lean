/-
The table `T(U, Π)` (def:table).

Paper: "Directed k Disjoint Shortest Paths Is Polynomial for Every Fixed k" (Saeed Amiri),
Section "The algorithm", subsections "Demands and the table" and "The leaf rule".

The table is defined by well-founded recursion on `|U|` using only the local rules of the paper:
the leaf rule (distinct labels and the pebble game of lem:pebbling) at point classes, and the
split rule (a split at two consecutive values of a star coordinate, an interface of at most
`3k - 4` (arc, demand) pairs satisfying (V1)--(V3), and the two smaller entries) otherwise.
It does not refer to solutions or to `S(U, Π)`.
-/
import DSPP.Demands
import DSPP.Pebbling

open Classical

namespace DSPP

variable {k : ℕ} [NeZero k] {V : Type*} [Fintype V] [DecidableEq V]

namespace Instance

variable (G : Instance V k)

/-! ### Leaf rule -/

/-- The total order `≺` of lem:pebbling: by `F_1`, ties broken by a fixed enumeration of `V`. -/
noncomputable def key (v : V) : Lex (ℝ × ℕ) := toLex (G.F 0 v, (Fintype.equivFin V v : ℕ))

theorem key_injective : Function.Injective G.key := by
  intro u v h
  have h2 := congrArg (fun p => (ofLex p).2) h
  simp only [key, ofLex_toLex] at h2
  exact (Fintype.equivFin V).injective (Fin.ext h2)

/-- The pebble game of lem:pebbling for the demands `Π` in `U`: pebble `δ = (l, a, b)` starts at
`a`, has goal `b`, and moves along the arcs of `D_l[U]`. -/
def pebbleWins (U : Finset V) (Dm : Finset (Demand V k)) : Prop :=
  Pebble.Wins (ι := {δ // δ ∈ Dm}) (fun r u w => u ∈ U ∧ w ∈ U ∧ G.inD r.1.1 u w) G.key
    (fun r => r.1.2.1) (fun r => r.1.2.2)

/-- No two demands of `Π` have the same label. -/
def DistinctLabels (Dm : Finset (Demand V k)) : Prop :=
  ∀ δ ∈ Dm, ∀ δ' ∈ Dm, δ.1 = δ'.1 → δ = δ'

/-- def:table, leaf rule: distinct labels, and `S(U, Π)` decided by the pebble game
(lem:pebbling). -/
def leafRule (U : Finset V) (Dm : Finset (Demand V k)) : Prop :=
  DistinctLabels Dm ∧ G.pebbleWins U Dm

/-! ### Splits -/

/-- All values of star coordinates at vertices. -/
noncomputable def allVals : Finset ℝ :=
  (Finset.univ : Finset (StarIdx k × V)).image fun p => G.starX p.1 p.2

/-- def:table.  `(j, α, α')` is a split of `U`: `α < α'` are consecutive elements of
`{X_{1j}(v) : v ∈ U}`. -/
def IsSplit (U : Finset V) (j : StarIdx k) (α α' : ℝ) : Prop :=
  α ∈ U.image (G.starX j) ∧ α' ∈ U.image (G.starX j) ∧ α < α' ∧
    ∀ v ∈ U, ¬ (α < G.starX j v ∧ G.starX j v < α')

/-- The splits of `U`. -/
noncomputable def splits (U : Finset V) : Finset (StarIdx k × ℝ × ℝ) :=
  (Finset.univ ×ˢ (G.allVals ×ˢ G.allVals)).filter fun sp => G.IsSplit U sp.1 sp.2.1 sp.2.2

/-- `U⁻ = {v ∈ U : X_{1j}(v) ≤ α}`. -/
noncomputable def Uminus (U : Finset V) (sp : StarIdx k × ℝ × ℝ) : Finset V :=
  U.filter fun v => G.starX sp.1 v ≤ sp.2.1

/-- `U⁺ = {v ∈ U : X_{1j}(v) ≥ α'}`. -/
noncomputable def Uplus (U : Finset V) (sp : StarIdx k × ℝ × ℝ) : Finset V :=
  U.filter fun v => sp.2.2 ≤ G.starX sp.1 v

theorem isSplit_of_mem_splits {U : Finset V} {sp : StarIdx k × ℝ × ℝ} (h : sp ∈ G.splits U) :
    G.IsSplit U sp.1 sp.2.1 sp.2.2 :=
  (Finset.mem_filter.1 h).2

theorem card_Uminus_lt {U : Finset V} {sp : StarIdx k × ℝ × ℝ} (h : sp ∈ G.splits U) :
    (G.Uminus U sp).card < U.card := by
  obtain ⟨-, h', hlt, -⟩ := G.isSplit_of_mem_splits h
  obtain ⟨v, hv, hvx⟩ := Finset.mem_image.1 h'
  apply Finset.card_lt_card
  rw [Uminus, Finset.filter_ssubset]
  exact ⟨v, hv, by rw [hvx]; exact not_le.2 hlt⟩

theorem card_Uplus_lt {U : Finset V} {sp : StarIdx k × ℝ × ℝ} (h : sp ∈ G.splits U) :
    (G.Uplus U sp).card < U.card := by
  obtain ⟨h', -, hlt, -⟩ := G.isSplit_of_mem_splits h
  obtain ⟨v, hv, hvx⟩ := Finset.mem_image.1 h'
  apply Finset.card_lt_card
  rw [Uplus, Finset.filter_ssubset]
  exact ⟨v, hv, by rw [hvx]; exact not_le.2 hlt⟩

/-! ### Interfaces -/

/-- An (arc, demand) pair. -/
abbrev ArcDemand (V : Type*) (k : ℕ) := (V × V) × Demand V k

/-- The pairs `(e, δ)` with `δ = (l, a, b) ∈ Π` and `e ∈ D_l` an arc with one end in `U⁻` and
the other in `U⁺`. -/
noncomputable def candPairs (U : Finset V) (Dm : Finset (Demand V k)) (sp : StarIdx k × ℝ × ℝ) :
    Finset (ArcDemand V k) :=
  ((Finset.univ : Finset (V × V)) ×ˢ Dm).filter fun p =>
    G.inD p.2.1 p.1.1 p.1.2 ∧
      ((p.1.1 ∈ G.Uminus U sp ∧ p.1.2 ∈ G.Uplus U sp) ∨
        (p.1.1 ∈ G.Uplus U sp ∧ p.1.2 ∈ G.Uminus U sp))

/-- def:table.  The interfaces for a split: sets of at most `3k - 4` candidate pairs. -/
noncomputable def interfaces (U : Finset V) (Dm : Finset (Demand V k))
    (sp : StarIdx k × ℝ × ℝ) : Finset (Finset (ArcDemand V k)) :=
  (G.candPairs U Dm sp).powerset.filter fun I => I.card ≤ 3 * k - 4

/-- The arcs assigned to the demand `δ` by the interface `I`. -/
noncomputable def assigned (I : Finset (ArcDemand V k)) (δ : Demand V k) : Finset (V × V) :=
  (I.filter fun p => p.2 = δ).image Prod.fst

/-- No two arcs assigned to `δ = (l, a, b)` have tails with the same value of `F_l`. -/
def TieFree (I : Finset (ArcDemand V k)) (δ : Demand V k) : Prop :=
  ∀ e ∈ assigned I δ, ∀ e' ∈ assigned I δ, G.F δ.1 e.1 = G.F δ.1 e'.1 → e = e'

/-- The arcs `e_1, ..., e_q` assigned to `δ = (l, a, b)`, sorted by `F_l` of their tails. -/
noncomputable def sortedArcs (I : Finset (ArcDemand V k)) (δ : Demand V k) : List (V × V) :=
  (assigned I δ).toList.mergeSort fun e e' => decide (G.F δ.1 e.1 ≤ G.F δ.1 e'.1)

/-- The chain of sub-demands `(l, a_0, b_0), ..., (l, a_q, b_q)` of `δ = (l, a, b)`, where
`e_s = (b_{s-1}, a_s)`, `a_0 = a` and `b_q = b`. -/
noncomputable def chain (I : Finset (ArcDemand V k)) (δ : Demand V k) : List (Demand V k) :=
  let es := G.sortedArcs I δ
  (List.zip (δ.2.1 :: es.map Prod.snd) (es.map Prod.fst ++ [δ.2.2])).map
    fun p => (δ.1, p.1, p.2)

/-- All sub-demands of all demands of `Π`, as a multiset. -/
noncomputable def allSub (Dm : Finset (Demand V k)) (I : Finset (ArcDemand V k)) :
    Multiset (Demand V k) :=
  Dm.val.bind fun δ => (G.chain I δ : Multiset (Demand V k))

/-- The ends of a sub-demand: `{a}` if `a = b`, otherwise `{a, b}`. -/
def demandEnds (σ : Demand V k) : Multiset V :=
  if σ.2.1 = σ.2.2 then {σ.2.1} else {σ.2.1, σ.2.2}

/-- The sub-demands on the side `U⁻` (multiset; with (V2) it has no repetitions). -/
noncomputable def subMinus (U : Finset V) (Dm : Finset (Demand V k)) (sp : StarIdx k × ℝ × ℝ)
    (I : Finset (ArcDemand V k)) : Multiset (Demand V k) :=
  (G.allSub Dm I).filter fun σ => σ.2.1 ∈ G.Uminus U sp

/-- The sub-demands on the side `U⁺`. -/
noncomputable def subPlus (U : Finset V) (Dm : Finset (Demand V k)) (sp : StarIdx k × ℝ × ℝ)
    (I : Finset (ArcDemand V k)) : Multiset (Demand V k) :=
  (G.allSub Dm I).filter fun σ => σ.2.1 ∈ G.Uplus U sp

/-- `Π⁻`. -/
noncomputable def PiMinus (U : Finset V) (Dm : Finset (Demand V k)) (sp : StarIdx k × ℝ × ℝ)
    (I : Finset (ArcDemand V k)) : Finset (Demand V k) :=
  (G.subMinus U Dm sp I).toFinset

/-- `Π⁺`. -/
noncomputable def PiPlus (U : Finset V) (Dm : Finset (Demand V k)) (sp : StarIdx k × ℝ × ℝ)
    (I : Finset (ArcDemand V k)) : Finset (Demand V k) :=
  (G.subPlus U Dm sp I).toFinset

/-- def:table.  The interface `I` is valid: the chains are well defined (no ties) and
(V1) each sub-demand has both ends on the same side;
(V2) the ends of all sub-demands are pairwise distinct, except `a_s = b_s` within one
sub-demand;
(V3) each side receives at most `P(k)` sub-demands. -/
def Valid (U : Finset V) (Dm : Finset (Demand V k)) (sp : StarIdx k × ℝ × ℝ)
    (I : Finset (ArcDemand V k)) : Prop :=
  (∀ δ ∈ Dm, G.TieFree I δ) ∧
  (∀ σ ∈ G.allSub Dm I, (σ.2.1 ∈ G.Uminus U sp ∧ σ.2.2 ∈ G.Uminus U sp) ∨
      (σ.2.1 ∈ G.Uplus U sp ∧ σ.2.2 ∈ G.Uplus U sp)) ∧
  ((G.allSub Dm I).bind demandEnds).Nodup ∧
  (G.subMinus U Dm sp I).card ≤ P k ∧ (G.subPlus U Dm sp I).card ≤ P k

/-! ### The table -/

/-- def:table.  The entry `T(U, Π)`, by recursion on `|U|`:
* leaf rule: if `U` is a point class, `T(U, Π)` holds iff the labels are distinct and the pebble
  game wins;
* split rule: otherwise, `T(U, Π)` holds iff for some split of `U` and some valid interface both
  `T(U⁻, Π⁻)` and `T(U⁺, Π⁺)` hold.
The table has entries for `U ∈ 𝒰` and `|Π| ≤ P(k)` with ends in `U` (`IsEntry`); the recursion
only visits entries from an entry. -/
noncomputable def Tab (U : Finset V) (Dm : Finset (Demand V k)) : Prop :=
  if G.IsPointClass U then G.leafRule U Dm
  else ∃ sp, ∃ _hsp : sp ∈ G.splits U, ∃ I ∈ G.interfaces U Dm sp, G.Valid U Dm sp I ∧
    Tab (G.Uminus U sp) (G.PiMinus U Dm sp I) ∧ Tab (G.Uplus U sp) (G.PiPlus U Dm sp I)
termination_by U.card
decreasing_by
  · exact G.card_Uminus_lt _hsp
  · exact G.card_Uplus_lt _hsp

/-- The unfolding equation of the table. -/
theorem Tab_eq (U : Finset V) (Dm : Finset (Demand V k)) :
    G.Tab U Dm = if G.IsPointClass U then G.leafRule U Dm
      else ∃ sp, ∃ _hsp : sp ∈ G.splits U, ∃ I ∈ G.interfaces U Dm sp, G.Valid U Dm sp I ∧
        G.Tab (G.Uminus U sp) (G.PiMinus U Dm sp I) ∧
        G.Tab (G.Uplus U sp) (G.PiPlus U Dm sp I) := by
  rw [Tab]

/-- The table entries: `U ∈ 𝒰` and `Π` a set of at most `P(k)` demands with ends in `U`. -/
def IsEntry (U : Finset V) (Dm : Finset (Demand V k)) : Prop :=
  U ∈ G.boxSets ∧ Dm.card ≤ P k ∧ ∀ δ ∈ Dm, δ.2.1 ∈ U ∧ δ.2.2 ∈ U

end Instance

end DSPP
