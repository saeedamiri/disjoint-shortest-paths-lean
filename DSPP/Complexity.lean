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

/-- The number of subsets of a set of `N` elements with at most `c` elements is at most
`(N + 1)^c`. -/
theorem card_subsets_le {α : Type*} (s : Finset α) (c : ℕ) :
    (s.powerset.filter fun t => t.card ≤ c).card ≤ (s.card + 1) ^ c := by
  calc (s.powerset.filter fun t => t.card ≤ c).card
      ≤ ((Finset.range (c + 1)).biUnion fun i => Finset.powersetCard i s).card := by
        apply Finset.card_le_card
        intro t ht
        simp only [Finset.mem_filter, Finset.mem_powerset] at ht
        simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_powersetCard]
        exact ⟨t.card, Nat.lt_succ_of_le ht.2, ht.1, rfl⟩
    _ ≤ ∑ i ∈ Finset.range (c + 1), (Finset.powersetCard i s).card := Finset.card_biUnion_le
    _ = ∑ i ∈ Finset.range (c + 1), s.card.choose i := by
        simp only [Finset.card_powersetCard]
    _ ≤ ∑ i ∈ Finset.range (c + 1), c.choose i * s.card ^ i := by
        apply Finset.sum_le_sum
        intro i hi
        have h1 : 1 ≤ c.choose i :=
          Nat.choose_pos (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))
        calc s.card.choose i ≤ s.card ^ i := Nat.choose_le_pow _ _
          _ = 1 * s.card ^ i := (one_mul _).symm
          _ ≤ c.choose i * s.card ^ i := Nat.mul_le_mul_right _ h1
    _ = (s.card + 1) ^ c := by
        rw [add_pow]
        apply Finset.sum_congr rfl
        intro i _
        simp [mul_comm]

theorem card_demand : Fintype.card (Demand V k) = k * Fintype.card V ^ 2 := by
  simp only [Demand, Fintype.card_prod, Fintype.card_fin]
  ring

theorem DistinctLabels.card_le {Dm : Finset (Demand V k)} (h : DistinctLabels Dm) :
    Dm.card ≤ k := by
  calc Dm.card ≤ (Finset.univ : Finset (Fin k)).card :=
        Finset.card_le_card_of_injOn Prod.fst (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
          (fun δ hδ δ' hδ' he => h δ hδ δ' hδ' he)
    _ = k := by simp

/-- At most `(n^2 + 1)^k` sets of demands have distinct labels: such a set is determined by
choosing, for each label, no demand or the two ends of the demand with that label. -/
theorem card_distinct_le :
    (Finset.univ.filter fun Dm : Finset (Demand V k) => DistinctLabels Dm).card ≤
      (Fintype.card V ^ 2 + 1) ^ k := by
  let Φ : Finset (Demand V k) → (Fin k → Option (V × V)) := fun Dm l =>
    if h : ∃ δ ∈ Dm, δ.1 = l then some (Classical.choose h).2 else none
  have hΦ : ∀ Dm : Finset (Demand V k), DistinctLabels Dm → ∀ δ ∈ Dm, Φ Dm δ.1 = some δ.2 := by
    intro Dm hD δ hδ
    have h : ∃ δ' ∈ Dm, δ'.1 = δ.1 := ⟨δ, hδ, rfl⟩
    simp only [Φ, dif_pos h]
    obtain ⟨h1, h2⟩ := Classical.choose_spec h
    rw [hD _ h1 δ hδ h2]
  have hΦ' : ∀ (Dm : Finset (Demand V k)) (l : Fin k) (x : V × V), Φ Dm l = some x →
      ∃ δ' ∈ Dm, δ'.1 = l ∧ δ'.2 = x := by
    intro Dm l x hx
    by_cases h : ∃ δ ∈ Dm, δ.1 = l
    · simp only [Φ, dif_pos h, Option.some.injEq] at hx
      obtain ⟨h1, h2⟩ := Classical.choose_spec h
      exact ⟨_, h1, h2, hx⟩
    · simp only [Φ, dif_neg h] at hx
      exact absurd hx (by simp)
  have hinj : ∀ Dm Dm' : Finset (Demand V k), DistinctLabels Dm → DistinctLabels Dm' →
      Φ Dm = Φ Dm' → Dm ⊆ Dm' := by
    intro Dm Dm' hD hD' he δ hδ
    have h1 : Φ Dm' δ.1 = some δ.2 := by rw [← he]; exact hΦ Dm hD δ hδ
    obtain ⟨δ', hδ', h2, h3⟩ := hΦ' Dm' _ _ h1
    have : δ' = δ := Prod.ext h2 h3
    rw [← this]; exact hδ'
  calc (Finset.univ.filter fun Dm : Finset (Demand V k) => DistinctLabels Dm).card
      ≤ (Finset.univ : Finset (Fin k → Option (V × V))).card := by
        apply Finset.card_le_card_of_injOn Φ (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
        intro Dm hDm Dm' hDm' he
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hDm hDm'
        exact Finset.Subset.antisymm (hinj _ _ hDm hDm' he) (hinj _ _ hDm' hDm he.symm)
    _ = (Fintype.card V ^ 2 + 1) ^ k := by
        simp [Fintype.card_fun, Fintype.card_option, sq]


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
  have h1 : G.entries ⊆ G.boxSets ×ˢ
      ((Finset.univ : Finset (Demand V k)).powerset.filter fun t => t.card ≤ P k) := by
    intro e he
    have h := (Finset.mem_filter.1 he).2
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ,
      true_and]
    exact ⟨h.1, h.2.1⟩
  calc G.entries.card ≤ _ := Finset.card_le_card h1
    _ = _ := Finset.card_product _ _
    _ ≤ _ := Nat.mul_le_mul G.lem_box_a.1 (by
        have := card_subsets_le (Finset.univ : Finset (Demand V k)) (P k)
        rwa [Finset.card_univ, card_demand] at this)

theorem isSplit_unique {U : Finset V} {j : StarIdx k} {α α' α'' : ℝ}
    (h : G.IsSplit U j α α') (h' : G.IsSplit U j α α'') : α' = α'' := by
  obtain ⟨-, ha', hlt, hno⟩ := h
  obtain ⟨-, ha'', hlt', hno'⟩ := h'
  rcases lt_trichotomy α' α'' with h1 | h1 | h1
  · obtain ⟨v, hv, hvx⟩ := Finset.mem_image.1 ha'
    exact absurd ⟨by rw [hvx]; exact hlt, by rw [hvx]; exact h1⟩ (hno' v hv)
  · exact h1
  · obtain ⟨v, hv, hvx⟩ := Finset.mem_image.1 ha''
    exact absurd ⟨by rw [hvx]; exact hlt', by rw [hvx]; exact h1⟩ (hno v hv)

/-- lem:time, splits: at most `(k-1) n` splits of a set `U`. -/
theorem card_splits_le (U : Finset V) : (G.splits U).card ≤ (k - 1) * Fintype.card V := by
  let nxt : StarIdx k → ℝ → ℝ := fun j a =>
    if h : ∃ a', G.IsSplit U j a a' then Classical.choose h else 0
  have h1 : G.splits U ⊆ ((Finset.univ : Finset (StarIdx k)) ×ˢ U).image
      (fun p => (p.1, G.starX p.1 p.2, nxt p.1 (G.starX p.1 p.2))) := by
    intro sp hsp
    have hs := G.isSplit_of_mem_splits hsp
    obtain ⟨j, a, a'⟩ := sp
    have ha := hs.1
    obtain ⟨v, hv, hvx⟩ := Finset.mem_image.1 ha
    refine Finset.mem_image.2 ⟨(j, v), by simp [hv], ?_⟩
    have hex : ∃ a', G.IsSplit U j a a' := ⟨a', hs⟩
    have hn : nxt j a = a' := by
      simp only [nxt, dif_pos hex]
      exact G.isSplit_unique (Classical.choose_spec hex) hs
    simp only [hvx, hn]
  have hcard : Fintype.card (StarIdx k) = k - 1 := by
    simp [StarIdx, Fintype.card_subtype_compl]
  calc (G.splits U).card ≤ _ := Finset.card_le_card h1
    _ ≤ _ := Finset.card_image_le
    _ = (k - 1) * U.card := by rw [Finset.card_product, Finset.card_univ, hcard]
    _ ≤ (k - 1) * Fintype.card V := Nat.mul_le_mul_left _ (Finset.card_le_univ U)

/-- lem:time, interfaces: at most `(n^2 P(k) + 1)^{3k-4}` interfaces for a split, when
`|Π| ≤ P(k)`. -/
theorem card_interfaces_le (U : Finset V) (Dm : Finset (Demand V k)) (hDm : Dm.card ≤ P k)
    (sp : StarIdx k × ℝ × ℝ) :
    (G.interfaces U Dm sp).card ≤ (Fintype.card V ^ 2 * P k + 1) ^ (3 * k - 4) := by
  have hc : (G.candPairs U Dm sp).card ≤ Fintype.card V ^ 2 * P k := by
    calc (G.candPairs U Dm sp).card
        ≤ (((Finset.univ : Finset (V × V)) ×ˢ Dm)).card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = Fintype.card V * Fintype.card V * Dm.card := by
          rw [Finset.card_product, Finset.card_univ, Fintype.card_prod]
      _ ≤ Fintype.card V ^ 2 * P k := by rw [sq]; exact Nat.mul_le_mul_left _ hDm
  calc (G.interfaces U Dm sp).card
      ≤ (G.candPairs U Dm sp).card.succ ^ (3 * k - 4) := card_subsets_le _ _
    _ ≤ _ := Nat.pow_le_pow_left (by omega) _

/-- lem:time, split rule: the work is at most
`f₁(k) · n^{2(k-1)} · n^{2P(k)} · n · n^{2(3k-4)}`. -/
theorem splitWork_le :
    G.splitWork ≤ ((k - 1) * (k + 1) ^ P k * (P k + 1) ^ (3 * k - 4)) *
      Fintype.card V ^ (2 * (k - 1) + 2 * P k + 1 + 2 * (3 * k - 4)) := by
  have hn : 1 ≤ Fintype.card V := Fintype.card_pos_iff.2 ⟨G.s 0⟩
  have hn2 : 1 ≤ Fintype.card V ^ 2 := Nat.one_le_pow _ _ hn
  have hstep : ∀ e ∈ G.entries, ∑ sp ∈ G.splits e.1, (G.interfaces e.1 e.2 sp).card ≤
      ((k - 1) * Fintype.card V) * (Fintype.card V ^ 2 * P k + 1) ^ (3 * k - 4) := by
    intro e he
    have h := (Finset.mem_filter.1 he).2
    calc ∑ sp ∈ G.splits e.1, (G.interfaces e.1 e.2 sp).card
        ≤ ∑ sp ∈ G.splits e.1, (Fintype.card V ^ 2 * P k + 1) ^ (3 * k - 4) :=
          Finset.sum_le_sum fun sp _ => G.card_interfaces_le e.1 e.2 h.2.1 sp
      _ = (G.splits e.1).card * (Fintype.card V ^ 2 * P k + 1) ^ (3 * k - 4) := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ _ := Nat.mul_le_mul_right _ (G.card_splits_le _)
  calc G.splitWork
      ≤ ∑ e ∈ G.entries, ((k - 1) * Fintype.card V) * (Fintype.card V ^ 2 * P k + 1) ^ (3 * k - 4) :=
        Finset.sum_le_sum hstep
    _ = G.entries.card * (((k - 1) * Fintype.card V) *
          (Fintype.card V ^ 2 * P k + 1) ^ (3 * k - 4)) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ (Fintype.card V ^ (2 * (k - 1)) * (k * Fintype.card V ^ 2 + 1) ^ P k) *
          (((k - 1) * Fintype.card V) * (Fintype.card V ^ 2 * P k + 1) ^ (3 * k - 4)) :=
        Nat.mul_le_mul_right _ G.card_entries_le
    _ ≤ (Fintype.card V ^ (2 * (k - 1)) * ((k + 1) * Fintype.card V ^ 2) ^ P k) *
          (((k - 1) * Fintype.card V) * ((P k + 1) * Fintype.card V ^ 2) ^ (3 * k - 4)) := by
        have e1 : k * Fintype.card V ^ 2 + 1 ≤ (k + 1) * Fintype.card V ^ 2 := by nlinarith
        have e2 : Fintype.card V ^ 2 * P k + 1 ≤ (P k + 1) * Fintype.card V ^ 2 := by nlinarith
        gcongr
    _ = _ := by
        rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul]
        ring

/-- lem:time, leaf rule: at most `n` point classes, at most `(n^2+1)^k` demand sets with
distinct labels, pebble-game graphs of size at most `n^{k+1}`. -/
theorem leafWork_le :
    G.leafWork ≤ Fintype.card V * (Fintype.card V ^ 2 + 1) ^ k * Fintype.card V ^ (k + 1) := by
  have hn : 1 ≤ Fintype.card V := Fintype.card_pos_iff.2 ⟨G.s 0⟩
  have hsub : G.entries.filter (fun e => G.IsPointClass e.1 ∧ DistinctLabels e.2) ⊆
      ((Finset.univ : Finset V).image G.pointClass) ×ˢ
        (Finset.univ.filter fun Dm : Finset (Demand V k) => DistinctLabels Dm) := by
    intro e he
    obtain ⟨-, ⟨v, hv⟩, hd⟩ := Finset.mem_filter.1 he
    have he' := (Finset.mem_filter.1 (Finset.mem_filter.1 he).1).2
    simp only [Finset.mem_product, Finset.mem_image, Finset.mem_univ, true_and,
      Finset.mem_filter]
    exact ⟨⟨v, hv.symm⟩, hd⟩
  have hF : (G.entries.filter (fun e => G.IsPointClass e.1 ∧ DistinctLabels e.2)).card ≤
      Fintype.card V * (Fintype.card V ^ 2 + 1) ^ k := by
    calc _ ≤ _ := Finset.card_le_card hsub
      _ = _ := Finset.card_product _ _
      _ ≤ _ := Nat.mul_le_mul
          (Finset.card_image_le.trans (by rw [Finset.card_univ])) card_distinct_le
  calc G.leafWork
      ≤ ∑ e ∈ G.entries.filter (fun e => G.IsPointClass e.1 ∧ DistinctLabels e.2),
          Fintype.card V ^ (k + 1) := by
        apply Finset.sum_le_sum
        intro e he
        exact Nat.pow_le_pow_right hn (Nat.succ_le_succ (Finset.mem_filter.1 he).2.2.card_le)
    _ = _ := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ _ := Nat.mul_le_mul_right _ hF

end Instance

/-- The exponent of lem:time: `2(k-1) + 2P(k) + 1 + 2(3k-4) = 6k^2 - 4k - 1` for `k ≥ 2`. -/
theorem exponent_eq (k : ℕ) (hk : 2 ≤ k) :
    2 * (k - 1) + 2 * P k + 1 + 2 * (3 * k - 4) = 6 * k ^ 2 - 4 * k - 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  have h1 : 3 * (2 + m) - 4 = 3 * m + 2 := by omega
  have h3 : 2 + m - 1 = m + 1 := by omega
  have h2 : 6 * (2 + m) ^ 2 - 4 * (2 + m) - 1 = 6 * m ^ 2 + 20 * m + 15 := by
    have : 6 * (2 + m) ^ 2 = 6 * m ^ 2 + 20 * m + 16 + 4 * (2 + m) := by ring
    omega
  rw [h2, P, h1, h3]; ring

/-- lem:time.  The table is computed with work `f(k) · n^{6k^2-4k-1}` for a function `f` of `k`
alone. -/
theorem lem_time : ∃ f : ℕ → ℕ, ∀ (k : ℕ) [NeZero k] (V : Type) [Fintype V] [DecidableEq V]
    (G : Instance V k),
    G.splitWork + G.leafWork ≤ f k * Fintype.card V ^ (6 * k ^ 2 - 4 * k - 1) := by
  refine ⟨fun k => (k - 1) * (k + 1) ^ P k * (P k + 1) ^ (3 * k - 4) + 2 ^ k, ?_⟩
  intro k _ V _ _ G
  have hk := G.two_le_k
  have hn : 1 ≤ Fintype.card V := Fintype.card_pos_iff.2 ⟨G.s 0⟩
  have h1 := G.splitWork_le
  rw [exponent_eq k hk] at h1
  have h2 := G.leafWork_le
  have h3 : G.leafWork ≤ 2 ^ k * Fintype.card V ^ (6 * k ^ 2 - 4 * k - 1) := by
    have e1 : Fintype.card V ^ 2 + 1 ≤ 2 * Fintype.card V ^ 2 := by
      have := Nat.one_le_pow 2 (Fintype.card V) hn
      omega
    have e2 : 3 * k + 2 ≤ 6 * k ^ 2 - 4 * k - 1 := by
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
      have : 6 * (2 + m) ^ 2 = 6 * m ^ 2 + 20 * m + 16 + 4 * (2 + m) := by ring
      omega
    calc G.leafWork ≤ Fintype.card V * (Fintype.card V ^ 2 + 1) ^ k * Fintype.card V ^ (k + 1) := h2
      _ ≤ Fintype.card V * (2 * Fintype.card V ^ 2) ^ k * Fintype.card V ^ (k + 1) := by
          gcongr
      _ = 2 ^ k * Fintype.card V ^ (3 * k + 2) := by
          rw [mul_pow, ← pow_mul]
          ring
      _ ≤ 2 ^ k * Fintype.card V ^ (6 * k ^ 2 - 4 * k - 1) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hn e2)
  calc G.splitWork + G.leafWork ≤ _ := add_le_add h1 h3
    _ = _ := by ring

end DSPP
