/-
Demands and the statement `S(U, Π)` (def:S).

Paper: "Directed k Disjoint Shortest Paths Is Polynomial for Every Fixed k" (Saeed Amiri),
Section "The algorithm", subsection "Demands and the table".
-/
import DSPP.Boxes

open Classical

namespace DSPP

/-- A demand `(l, a, b)`: label `l`, ends `a` and `b`. -/
abbrev Demand (V : Type*) (k : ℕ) := Fin k × V × V

variable {k : ℕ} [NeZero k] {V : Type*} [Fintype V] [DecidableEq V]

namespace Instance

variable (G : Instance V k)

/-- `R` leads from `a` to `b` in `D_l[U]`: a simple path from `a` to `b` whose vertices lie in
`U` and whose arcs lie in `D_l` (for `a = b` it is the one-vertex path `a`). -/
def IsDemandPath (U : Finset V) (δ : Demand V k) (R : List V) : Prop :=
  R.head? = some δ.2.1 ∧ R.getLast? = some δ.2.2 ∧ R.Nodup ∧ (∀ v ∈ R, v ∈ U) ∧
    R.IsChain (G.inD δ.1)

/-- def:S.  `S(U, Π)`: there are pairwise vertex-disjoint paths `R_δ`, `δ ∈ Π`, where `R_δ`
for `δ = (l, a, b)` leads from `a` to `b` with all vertices in `U` and all arcs in `D_l[U]`. -/
def Sem (U : Finset V) (Dm : Finset (Demand V k)) : Prop :=
  ∃ R : Demand V k → List V,
    (∀ δ ∈ Dm, G.IsDemandPath U δ (R δ)) ∧
    ∀ δ ∈ Dm, ∀ δ' ∈ Dm, δ ≠ δ' → ∀ v ∈ R δ, v ∉ R δ'

/-- The paths `R` witness `S(U, Π)`. -/
def SemBy (U : Finset V) (Dm : Finset (Demand V k)) (R : Demand V k → List V) : Prop :=
  (∀ δ ∈ Dm, G.IsDemandPath U δ (R δ)) ∧
    ∀ δ ∈ Dm, ∀ δ' ∈ Dm, δ ≠ δ' → ∀ v ∈ R δ, v ∉ R δ'

theorem sem_iff_semBy (U : Finset V) (Dm : Finset (Demand V k)) :
    G.Sem U Dm ↔ ∃ R, G.SemBy U Dm R := Iff.rfl

/-- The root demands `Π_0 = {(l, s_l, t_l)}`. -/
noncomputable def Pi0 : Finset (Demand V k) := Finset.univ.image fun l => (l, G.s l, G.t l)

/-- Paths for the root demands, read by label, are a solution (by lem:Di (b)). -/
theorem semBy_root_isSolution {R : Demand V k → List V} (h : G.SemBy Finset.univ G.Pi0 R) :
    G.IsSolution fun l => R (l, G.s l, G.t l) := by
  obtain ⟨hR, hdisj⟩ := h
  have hl : ∀ l, ((l, G.s l, G.t l) : Demand V k) ∈ G.Pi0 := by
    intro l
    simp only [Pi0, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨l, rfl⟩
  refine ⟨fun i => ?_, fun i j hij v hv => ?_⟩
  · obtain ⟨h1, h2, h3, _, h5⟩ := hR _ (hl i)
    have hp : G.IsPath (R (i, G.s i, G.t i)) (G.s i) (G.t i) :=
      ⟨⟨h1, h2, h5.imp fun _ _ h => h.1⟩, h3⟩
    exact (G.lem_Di_b hp).mpr h5
  · refine hdisj _ (hl i) _ (hl j) ?_ v hv
    intro h
    exact hij (by simpa using congrArg Prod.fst h)

/-- Text after def:S: the instance has a solution iff `S(V, Π_0)` (by lem:Di (b)). -/
theorem sem_root_iff : G.Sem Finset.univ G.Pi0 ↔ G.HasSolution := by
  have hmem : ∀ δ ∈ G.Pi0, ∃ l, δ = (l, G.s l, G.t l) := by
    intro δ hδ
    simp only [Pi0, Finset.mem_image, Finset.mem_univ, true_and] at hδ
    obtain ⟨l, rfl⟩ := hδ
    exact ⟨l, rfl⟩
  have hl : ∀ l, ((l, G.s l, G.t l) : Demand V k) ∈ G.Pi0 := by
    intro l
    simp only [Pi0, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨l, rfl⟩
  constructor
  · rintro ⟨R, hR⟩
    exact ⟨_, G.semBy_root_isSolution hR⟩
  · rintro ⟨P, hP, hdisj⟩
    refine ⟨fun δ => P δ.1, fun δ hδ => ?_, fun δ hδ δ' hδ' hne v hv => ?_⟩
    · obtain ⟨l, rfl⟩ := hmem δ hδ
      have hsh := hP l
      have hp := hsh.1
      have hc := (G.lem_Di_b hp).mp hsh
      exact ⟨hp.1.1, hp.1.2.1, hp.2, fun v _ => Finset.mem_univ v, hc⟩
    · obtain ⟨l, rfl⟩ := hmem δ hδ
      obtain ⟨l', rfl⟩ := hmem δ' hδ'
      have : l ≠ l' := by
        rintro rfl
        exact hne rfl
      exact hdisj l l' this v hv

end Instance

end DSPP
