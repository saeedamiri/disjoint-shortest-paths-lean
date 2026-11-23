/-
The shortest-path DAGs `D_i` (def:Di, lem:Di).

Paper: "Directed k Disjoint Shortest Paths Is Polynomial for Every Fixed k" (Saeed Amiri),
Section "Preliminaries".
-/
import DSPP.Basic

open Classical

namespace DSPP

variable {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}

namespace Instance

variable (G : Instance V k)

/-- def:Di.  The arc `(u,v)` lies in `D_i`: `d(s_i,u) + ℓ(u,v) + d(v,t_i) = d_i`.
The paper uses extended reals; an equation with the finite value `d_i` forces both distances
on the left to be finite, which is what the two `Reach` conditions say.  If `t_i` is not
reachable from `s_i`, then `D_i` is empty. -/
def inD (i : Fin k) (u v : V) : Prop :=
  G.arc u v ∧ G.Reach (G.s i) u ∧ G.Reach v (G.t i) ∧
    G.dist (G.s i) u + G.len u v + G.dist v (G.t i) = G.d i

/-- def:Di.  A `D_i`-path: a (simple) path all of whose arcs lie in `D_i`.  Its end vertices
are arbitrary. -/
def IsDPath (i : Fin k) (R : List V) : Prop :=
  R ≠ [] ∧ R.IsChain (G.inD i) ∧ R.Nodup

/-- lem:Di (a). -/
theorem lem_Di_a {i : Fin k} {u v : V} (h : G.inD i u v) :
    G.Reach (G.s i) v ∧ G.dist (G.s i) v = G.dist (G.s i) u + G.len u v ∧
      G.dist (G.s i) v ≤ G.d i ∧
    G.Reach u (G.t i) ∧ G.dist u (G.t i) = G.len u v + G.dist v (G.t i) ∧
      G.dist u (G.t i) ≤ G.d i := by
  sorry

/-- lem:Di (b).  A path from `s_i` to `t_i` is a shortest path if and only if it is a
`D_i`-path. -/
theorem lem_Di_b {i : Fin k} {R : List V} (h : G.IsPath R (G.s i) (G.t i)) :
    G.IsShortestPath R (G.s i) (G.t i) ↔ R.IsChain (G.inD i) := by
  sorry

/-- lem:Di (c).  `D_i` is acyclic. -/
theorem lem_Di_c (i : Fin k) (u : V) : ¬ Relation.TransGen (G.inD i) u u := by
  sorry

end Instance

end DSPP
