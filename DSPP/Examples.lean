/-
An explicit instance, showing that the hypotheses of the main theorem are satisfiable.

Paper: "Directed k Disjoint Shortest Paths Is Polynomial for Every Fixed k" (Saeed Amiri).
-/
import DSPP.Basic

namespace DSPP

/-- Two disjoint arcs `0 → 1` and `2 → 3` of length `1`, with terminals `s = (0, 2)` and
`t = (1, 3)`. -/
example : Nonempty (Instance (Fin 4) 2) :=
  ⟨{ arc := fun u v => (u = 0 ∧ v = 1) ∨ (u = 2 ∧ v = 3)
     len := fun _ _ => 1
     len_pos := fun _ _ _ => one_pos
     s := ![0, 2]
     t := ![1, 3]
     terminals_injective := by decide
     two_le_k := le_rfl }⟩

end DSPP
