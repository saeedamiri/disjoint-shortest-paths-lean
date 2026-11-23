/-
The pebble game of Fortune, Hopcroft and Wyllie on acyclic relations (the argument of
lem:pebbling), in a general form independent of the shortest-paths setting.

Paper: "Directed k Disjoint Shortest Paths Is Polynomial for Every Fixed k" (Saeed Amiri),
Section "The algorithm", subsection "The leaf rule: pebbling inside a point class".

Setting: pebbles `r : ι`, pebble `r` moves along the relation `E r` on `W`; every arc of every
`E r` increases `key`, an injective map into a linear order (the total order `≺` of the paper).
-/
import Mathlib

open Classical

namespace DSPP

namespace Pebble

variable {ι W κ : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder κ]
variable (E : ι → W → W → Prop) (key : W → κ) (a b : ι → W)

/-- One move of the game from the state `x` to the state `y`: the unfinished pebble `r`
(`x r ≠ b r`) whose position is `≺`-smallest among the unfinished pebbles moves along an arc of
`E r` to a vertex not occupied by another pebble. -/
def Move (x y : ι → W) : Prop :=
  ∃ r, x r ≠ b r ∧ (∀ r', x r' ≠ b r' → key (x r) ≤ key (x r')) ∧
    ∃ w, E r (x r) w ∧ (∀ r', r' ≠ r → x r' ≠ w) ∧ y = Function.update x r w

/-- The game is won: the start `a` is a state (pairwise distinct positions), and the goal `b`
is reachable from `a` by moves. -/
def Wins : Prop := Function.Injective a ∧ Relation.ReflTransGen (Move E key b) a b

/-- Pairwise vertex-disjoint paths: `P r` leads from `a r` to `b r` along arcs of `E r`. -/
def DisjointPaths : Prop :=
  ∃ P : ι → List W,
    (∀ r, (P r).head? = some (a r) ∧ (P r).getLast? = some (b r) ∧
      (P r).IsChain (E r) ∧ (P r).Nodup) ∧
    ∀ r r', r ≠ r' → ∀ w ∈ P r, w ∉ P r'

/-- Fortune--Hopcroft--Wyllie (the argument of lem:pebbling): if every arc increases `key`,
the game is won if and only if there are pairwise disjoint paths. -/
theorem fhw (hkey : Function.Injective key) (hE : ∀ r u v, E r u v → key u < key v) :
    Wins E key a b ↔ DisjointPaths E a b := by
  sorry

/-- Size of the game graph (lem:pebbling, running time): at most `|W|^{|ι|}` states. -/
theorem card_states [Fintype W] : Fintype.card (ι → W) = Fintype.card W ^ Fintype.card ι := by
  simp

/-- Size of the game graph (lem:pebbling, running time): from an injective state there are at
most `|W|` moves. -/
theorem card_moves_le [Fintype W] [DecidableEq W] (hkey : Function.Injective key) (x : ι → W)
    (hx : Function.Injective x) :
    (Finset.univ.filter fun y => Move E key b x y).card ≤ Fintype.card W := by
  sorry

end Pebble

end DSPP
