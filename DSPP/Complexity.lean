/-
The size of the table computation (lem:time), as cardinality bounds.

Paper: "Directed k Disjoint Shortest Paths Is Polynomial for Every Fixed k" (Saeed Amiri),
Section "The algorithm", subsection "Running time and proof of the main theorem".

No machine model: the work of the split rule is the number of triples
(entry, split, interface) the rule inspects, each handled in time depending on `k` only; the work
of the leaf rule is the size `n^p · n` of the pebble-game graph per leaf entry.  The preprocessing
(Dijkstra, sorting) is not counted.
-/
import DSPP.Table

open Classical

namespace DSPP

variable {k : ℕ} [NeZero k] {V : Type*} [Fintype V] [DecidableEq V]

namespace Instance

variable (G : Instance V k)

/-- The table entries `(U, Π)`: `U ∈ 𝒰`, `|Π| ≤ P(k)`, ends of `Π` in `U`. -/
noncomputable def entries : Finset (Finset V × Finset (Demand V k)) :=
  (G.boxSets ×ˢ Finset.univ).filter fun e => G.IsEntry e.1 e.2

/-- The work of the split rule: the number of (entry, split, interface) triples. -/
noncomputable def splitWork : ℕ :=
  ∑ e ∈ G.entries, ∑ sp ∈ G.splits e.1, (G.interfaces e.1 e.2 sp).card

/-- The work of the leaf rule: for every entry at a point class with distinct labels, the size
`n^{|Π|} · n` of the pebble-game graph (states times moves per state). -/
noncomputable def leafWork : ℕ :=
  ∑ e ∈ G.entries.filter (fun e => G.IsPointClass e.1 ∧ DistinctLabels e.2),
    Fintype.card V ^ (e.2.card + 1)

/-- lem:time, entries: at most `n^{2(k-1)} (k n^2 + 1)^{P(k)}` entries. -/
theorem card_entries_le :
    G.entries.card ≤ Fintype.card V ^ (2 * (k - 1)) * (k * Fintype.card V ^ 2 + 1) ^ P k := by
  sorry

/-- lem:time, splits: at most `(k-1) n` splits of a set `U`. -/
theorem card_splits_le (U : Finset V) : (G.splits U).card ≤ (k - 1) * Fintype.card V := by
  sorry

/-- lem:time, interfaces: at most `(n^2 P(k) + 1)^{3k-4}` interfaces for a split, when
`|Π| ≤ P(k)`. -/
theorem card_interfaces_le (U : Finset V) (Dm : Finset (Demand V k)) (hDm : Dm.card ≤ P k)
    (sp : StarIdx k × ℝ × ℝ) :
    (G.interfaces U Dm sp).card ≤ (Fintype.card V ^ 2 * P k + 1) ^ (3 * k - 4) := by
  sorry

/-- lem:time, split rule: the work is at most
`f₁(k) · n^{2(k-1)} · n^{2P(k)} · n · n^{2(3k-4)}`. -/
theorem splitWork_le :
    G.splitWork ≤ ((k - 1) * (k + 1) ^ P k * (P k + 1) ^ (3 * k - 4)) *
      Fintype.card V ^ (2 * (k - 1) + 2 * P k + 1 + 2 * (3 * k - 4)) := by
  sorry

/-- lem:time, leaf rule: at most `n` point classes, at most `(n^2+1)^k` demand sets with
distinct labels, pebble-game graphs of size at most `n^{k+1}`. -/
theorem leafWork_le :
    G.leafWork ≤ Fintype.card V * (Fintype.card V ^ 2 + 1) ^ k * Fintype.card V ^ (k + 1) := by
  sorry

end Instance

/-- The exponent of lem:time: `2(k-1) + 2P(k) + 1 + 2(3k-4) = 6k^2 - 4k - 1` for `k ≥ 2`. -/
theorem exponent_eq (k : ℕ) (hk : 2 ≤ k) :
    2 * (k - 1) + 2 * P k + 1 + 2 * (3 * k - 4) = 6 * k ^ 2 - 4 * k - 1 := by
  sorry

/-- lem:time.  The table is computed with work `f(k) · n^{6k^2-4k-1}` for a function `f` of `k`
alone. -/
theorem lem_time : ∃ f : ℕ → ℕ, ∀ (k : ℕ) [NeZero k] (V : Type) [Fintype V] [DecidableEq V]
    (G : Instance V k),
    G.splitWork + G.leafWork ≤ f k * Fintype.card V ^ (6 * k ^ 2 - 4 * k - 1) := by
  sorry

end DSPP
