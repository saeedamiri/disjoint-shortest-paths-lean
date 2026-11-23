/-
lem:pebbling: the leaf rule decides `S(U, Π)` inside a point class.

Paper: "Directed k Disjoint Shortest Paths Is Polynomial for Every Fixed k" (Saeed Amiri),
Section "The algorithm", subsection "The leaf rule: pebbling inside a point class".
-/
import DSPP.Table

open Classical

namespace DSPP

variable {k : ℕ} [NeZero k] {V : Type*} [Fintype V] [DecidableEq V]

namespace Instance

variable (G : Instance V k)

/-- lem:pebbling.  Let `U` be a point class and `Π` a set of demands with ends in `U`.  Then
the pebble game wins if and only if `S(U, Π)` holds.  (The running time `O(p n^{p+1})` is the
size of the game graph, `Pebble.card_states` and `Pebble.card_moves_le`.) -/
theorem lem_pebbling (U : Finset V) (hU : G.IsPointClass U) (Dm : Finset (Demand V k))
    (hends : ∀ δ ∈ Dm, δ.2.1 ∈ U ∧ δ.2.2 ∈ U) :
    G.pebbleWins U Dm ↔ G.Sem U Dm := by
  sorry

end Instance

end DSPP
