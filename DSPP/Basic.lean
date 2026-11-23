/-
Instances, walks, paths, distances and solutions.

Formalization of "Directed k Disjoint Shortest Paths Is Polynomial for Every Fixed k"
(Saeed Amiri), Section "Preliminaries", subsection "Instances and shortest-path DAGs".
-/
import Mathlib

open Classical

namespace DSPP

/-- An instance of the directed `k` disjoint shortest paths problem.

The vertex set is the finite type `V`, `n = Fintype.card V`.  Arcs are given by the relation
`arc`, so there are no parallel arcs (the paper removes them without loss of generality, see
`DEVIATIONS.md`).  The terminal pairs are `(s l, t l)` for `l : Fin k`; the `2k` terminals are
pairwise distinct. -/
structure Instance (V : Type*) [Fintype V] [DecidableEq V] (k : ℕ) where
  /-- The arc relation of the directed graph. -/
  arc : V → V → Prop
  /-- The length function; only its values on arcs matter. -/
  len : V → V → ℝ
  /-- Lengths are strictly positive on arcs. -/
  len_pos : ∀ u v, arc u v → 0 < len u v
  /-- Sources. -/
  s : Fin k → V
  /-- Sinks. -/
  t : Fin k → V
  /-- The `2k` terminals are pairwise distinct. -/
  terminals_injective : Function.Injective (Sum.elim s t)
  /-- At least two pairs. -/
  two_le_k : 2 ≤ k

variable {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}

/-- The arcs `(v_q, v_{q+1})` of a vertex sequence, in order. -/
def arcs (R : List V) : List (V × V) := R.zip R.tail

namespace Instance

variable (G : Instance V k)

/-- `R` is a walk from `a` to `b`: a non-empty vertex sequence starting at `a`, ending at `b`,
with consecutive vertices joined by arcs. -/
def IsWalk (R : List V) (a b : V) : Prop :=
  R.head? = some a ∧ R.getLast? = some b ∧ R.IsChain G.arc

/-- `R` is a (simple, directed) path from `a` to `b`.  A path may consist of a single vertex. -/
def IsPath (R : List V) (a b : V) : Prop :=
  G.IsWalk R a b ∧ R.Nodup

/-- The length of a vertex sequence: the sum of the lengths of its arcs. -/
noncomputable def wlen (R : List V) : ℝ :=
  ((arcs R).map fun e => G.len e.1 e.2).sum

/-- `b` is reachable from `a`. -/
def Reach (a b : V) : Prop := ∃ R, G.IsWalk R a b

/-- The distance `d(a,b)`: the infimum of the lengths of the walks from `a` to `b`.  It is only
meaningful when `G.Reach a b`; for unreachable pairs its value (`0`) is never used, every
statement that involves it also involves `Reach`.  With positive lengths the infimum over walks
equals the minimum over paths (`dist_eq_min_path`). -/
noncomputable def dist (a b : V) : ℝ :=
  sInf {x | ∃ R, G.IsWalk R a b ∧ G.wlen R = x}

/-- `d_i = d(s_i, t_i)`. -/
noncomputable def d (i : Fin k) : ℝ := G.dist (G.s i) (G.t i)

/-- `R` is a shortest path from `a` to `b`: a path that is not longer than any other path from
`a` to `b`. -/
def IsShortestPath (R : List V) (a b : V) : Prop :=
  G.IsPath R a b ∧ ∀ R', G.IsPath R' a b → G.wlen R ≤ G.wlen R'

/-- A solution: pairwise vertex-disjoint paths `P_1, ..., P_k`, where `P_i` is a shortest
`s_i`--`t_i` path. -/
def IsSolution (P : Fin k → List V) : Prop :=
  (∀ i, G.IsShortestPath (P i) (G.s i) (G.t i)) ∧
    ∀ i j, i ≠ j → ∀ v ∈ P i, v ∉ P j

/-- The instance has a solution. -/
def HasSolution : Prop := ∃ P : Fin k → List V, G.IsSolution P

/-! ### Basic facts about walks and distances -/

/-- Lengths of walks are non-negative. -/
theorem wlen_nonneg {R : List V} {a b : V} (h : G.IsWalk R a b) : 0 ≤ G.wlen R := by
  sorry

/-- The distance is a lower bound for the length of every walk. -/
theorem dist_le_wlen {R : List V} {a b : V} (h : G.IsWalk R a b) : G.dist a b ≤ G.wlen R := by
  sorry

/-- Distances are non-negative. -/
theorem dist_nonneg (a b : V) : 0 ≤ G.dist a b := by
  sorry

/-- Triangle inequality along an arc. -/
theorem dist_le_dist_add_len {a u v : V} (hu : G.Reach a u) (huv : G.arc u v) :
    G.Reach a v ∧ G.dist a v ≤ G.dist a u + G.len u v := by
  sorry

/-- Triangle inequality along an arc, distances to a target. -/
theorem dist_le_len_add_dist {u v b : V} (hv : G.Reach v b) (huv : G.arc u v) :
    G.Reach u b ∧ G.dist u b ≤ G.len u v + G.dist v b := by
  sorry

/-- Triangle inequality. -/
theorem dist_triangle {a u b : V} (h1 : G.Reach a u) (h2 : G.Reach u b) :
    G.Reach a b ∧ G.dist a b ≤ G.dist a u + G.dist u b := by
  sorry

/-- Shortcutting: every walk contains a path with the same ends that is not longer
(lengths are positive). -/
theorem exists_path_of_walk {W : List V} {a b : V} (h : G.IsWalk W a b) :
    ∃ R, G.IsPath R a b ∧ G.wlen R ≤ G.wlen W ∧ ∀ v ∈ R, v ∈ W := by
  sorry

/-- With positive lengths the distance is attained by a path. -/
theorem dist_eq_min_path {a b : V} (h : G.Reach a b) :
    ∃ R, G.IsPath R a b ∧ G.wlen R = G.dist a b := by
  sorry

/-- A path is shortest if and only if its length is the distance. -/
theorem isShortestPath_iff {R : List V} {a b : V} :
    G.IsShortestPath R a b ↔ G.IsPath R a b ∧ G.wlen R = G.dist a b := by
  sorry

end Instance

end DSPP
