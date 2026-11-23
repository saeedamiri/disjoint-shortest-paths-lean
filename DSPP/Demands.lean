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

/-- The root demands `Π_0 = {(l, s_l, t_l)}`. -/
noncomputable def Pi0 : Finset (Demand V k) := Finset.univ.image fun l => (l, G.s l, G.t l)

/-- Text after def:S: the instance has a solution iff `S(V, Π_0)` (by lem:Di (b)). -/
theorem sem_root_iff : G.Sem Finset.univ G.Pi0 ↔ G.HasSolution := by
  sorry

end Instance

end DSPP
