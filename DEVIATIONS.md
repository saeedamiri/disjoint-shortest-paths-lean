# Deviations from the paper

Paper: "Directed k Disjoint Shortest Paths Is Polynomial for Every Fixed k" (Saeed Amiri).
Labels below are the paper's LaTeX labels.

Every entry gives the paper's form, the Lean form, and why the Lean form is equivalent or
sufficient. The main theorem (`DSPP.thm_main`) and the table (`Instance.Tab`) follow the paper.

## Modelling choices (Basic.lean, ShortestDAG.lean, Potentials.lean)

1. **No parallel arcs.** The paper allows parallel arcs and then removes them without loss of
   generality (text after lem:Di). In Lean, arcs are a relation `arc : V → V → Prop` with
   lengths `len : V → V → ℝ`, so there are no parallel arcs from the start. This is the
   paper's normalized instance. The reduction step is not formalized.

2. **Distances.** The paper uses `d(u,v) ∈ ℝ≥0 ∪ {∞}`. Lean uses a predicate
   `Reach a b` and a real number `dist a b`, the infimum of walk lengths. Its value is 0 when
   `b` is not reachable, and every statement that uses it also uses `Reach`. `dist` is an
   infimum over walks, not paths. With positive lengths the two agree (`dist_eq_min_path`,
   `exists_path_of_walk`). `IsShortestPath` compares against all paths, as the paper does.

3. **`d_i` finite.** The paper assumes that every `d_i` is finite. Lean adds no such hypothesis.
   `inD i u v` (the arc `(u,v)` lies in `D_i`) requires `Reach (s i) u` and `Reach v (t i)`, so
   `D_i` is empty when `t_i` cannot be reached from `s_i`. Then lem:Di and (W0) still hold.
   `F_i` follows def:potentials with `min(∞, d_i) = d_i` and `max(-∞, 0) = 0`.
   `cor_correct` and `thm_main` hold without the assumption: if some `t_i` cannot be reached,
   both sides are false.

4. **Indices.** The paper's index `1` is `0 : Fin k`. The star indices `j = 2..k` form the type
   `StarIdx k = {j : Fin k // j ≠ 0}`, which has `k - 1` elements. Lemmas that need index `0`
   assume `[NeZero k]`. The field `Instance.two_le_k` gives `k ≥ 2`.

5. **lem:W12** is split into `lem_W1` and `lem_W2`.

## Cells and crossings (Cells.lean, Crossing.lean)

6. **Cells** are stored by their bounds (`Cell.lo`, `Cell.hi` on `StarIdx k`), and
   `Cell.carrier` is the point set. Extents are `sSup - sInf` over the carrier, as in def:cell.
   The children `C.lower j λ` and `C.upper j λ` clamp the new bound, so the bounds stay valid
   for every `λ`. In a hierarchy `a_j < λ < b_j`, the clamp has no effect, and the children are
   exactly `C ∩ {X_{1j} ≤ λ}` and `C ∩ {X_{1j} ≥ λ}` (lem:extent (c), `lem_extent_c`).

7. **def:N (crossing number).** The paper counts pairs `(l, t)` with `γ_l(t) ∈ C` and
   `X_{1j}(γ_l(t)) = λ`, where `γ_l` is a polygonal curve. Lean's `crossNum` is a finite
   count over arcs instead. It counts the pairs (path `l`, arc position of `R_l`) whose segment
   has its ends strictly on different sides of `λ` and whose crossing point
   (`crossPt`, linear interpolation) lies in `C`.
   - Why they agree: for generic `λ` a curve meets the hyperplane only in the interior of
     non-constant segments, at most once per segment, and exactly when the ends straddle `λ`.
   - Where this is stated: the paper's count is also defined (`curve`, `curveCount`, using
     `Set.ncard`), and `crossNum_eq_curveCount` states that the two agree for generic `λ`.
   - Arcs whose ends both lie outside `C` but whose crossing point lies in `C` are counted, as
     in the paper.

## Hierarchy (Hierarchy.lean, Averaging.lean, Termination.lean, Pieces.lean, HierarchyThm.lean)

8. **Hierarchy as data.** A hierarchy is an inductive binary tree `CutTree` with cuts
   `(j, λ)` at inner nodes. Its cells come from the root cell (`CutTree.nodes`). The paper
   writes the level condition as `min_C X_{1j} < λ < max_C X_{1j}`. Lean writes it as
   `C.lo j < λ < C.hi j`, which is the same condition by lem:extent (b).

9. **(H3) and lem:pieces: pieces only.** The paper bounds two quantities: the number of
   connected components of `γ_l⁻¹(C)`, and, as a consequence, the number of pieces.
   - What Lean states: only the pieces bound, `numPieces Rs (cellVerts C) ≤ P k`.
   - Why that suffices: lem:complete, and so the main theorem, uses only the pieces bound.
   - Proof: the charging argument of lem:pieces can be done arc by arc. A piece that does not
     start at `v_0` is charged to its entering arc. That arc crosses the level of some last
     half-space `h` at a point of `C ⊆ A_h`, so the arc is counted in `crossNum Rs A_h j_h λ_h`.
     Exits are charged in the same way.

10. **lem:pieces is stated for every hierarchy** with (H1) and (H2), not only for the tree
    of def:construction. The paper's proof says that these are the only facts it uses. The Lean
    statement is therefore stronger. It needs no `D_l`-path hypothesis on the paths.

11. **lem:averaging, discrete form.** The paper says: `N_C` agrees, except at finitely many
    `λ`, with a non-negative step function whose integral over `[m, M]` is at most `(3k-4)E`.
    - Lean (`lem_averaging`): there are a finite family of intervals `(a_s, b_s)` and a finite
      set `bad` such that `Σ_s |b_s - a_s| ≤ (3k-4)E`, and every generic `λ ∉ bad` has
      `N_C(λ) = #{s : λ strictly between a_s and b_s}`.
    - Why this is the same: the paper's step function is this sum of interval indicators (its
      proof builds exactly these intervals), and the integral is the sum of the lengths.
    - What replaces the measure step of cor:goodlevel: `exists_low_count`, a lemma about finite
      interval families with no measure theory. If the total length is less than
      `(c+1)(hi - lo)`, then some point of `(lo, hi)` that avoids a given finite set lies in at
      most `c` intervals.
    - Arithmetic: with `c = 3k - 4` and `(lo, hi) = (m + θE, M - θE)`,
      `(3k-3)(1-2θ)E = (3k - 4 + 1/k)E > (3k-4)E`.

12. **cor:goodlevel** concludes `IsGoodLevel`: generic, `a_j + θw ≤ λ ≤ b_j - θw`, and
    `crossNum ≤ 3k - 4`. Here `[m, M] = [a_j, b_j]` by lem:extent.

13. **lem:termination** is stated as well-foundedness of the relation "`C'` is a child of `C`
    by a step of def:construction" (`ConstrStep`), for every choice of good levels. This is what
    "the tree is finite" means for a tree built by choices. `exists_constructionTree` turns it
    into a finite `CutTree` that satisfies the construction rule.

14. **thm:hierarchy** is stated with an explicit root cell `C0` together with (H1)–(H4). (H3)
    is in the pieces-only form of item 9.

## The algorithm (Boxes.lean, Demands.lean, Pebbling.lean, Table.lean, Leaf.lean)

15. **Table domain.** In the paper, the table has entries only for `U ∈ 𝒰` and for sets `Π`
    of at most `P(k)` demands with ends in `U`. The Lean `Tab U Π` is defined for all `U` and
    `Π` by the same two rules. `IsEntry` marks the real entries, and the split rule moves from
    an entry only to entries: lem:box (d), (V1), (V3).
    - Split rule condition: the paper applies it when `U` meets at least two point classes.
      Lean applies it when `U` is not a point class (the `else` branch). For box sets the two
      conditions are equivalent by lem:box (e).

16. **Leaf rule.** The paper states the leaf rule as `T(U, Π) = S(U, Π)`, decided by
    lem:pebbling. Lean defines it directly by the pebble game: distinct labels and
    `pebbleWins`. This keeps the table free of any quantification over paths. `lem_pebbling`
    states that this equals `S(U, Π)` at point classes, so the definition is equivalent to the
    paper's.
    - The order `≺`: by `F_1`, with ties broken by a fixed enumeration of `V`
      (`Instance.key`). The paper allows any refinement of the `F_1` order.
    - The game: `Pebble.Wins` requires the start positions to be pairwise distinct, and moves
      keep them distinct. So distinct ends `b_r` are needed to reach the goal, as in the
      paper's proof.
    - Fortune–Hopcroft–Wyllie is stated generally in `Pebbling.lean` (`Pebble.fhw`), for
      relations whose arcs increase an injective key.

17. **Chains.** The arcs assigned to a demand are sorted by `List.mergeSort` on `F_l` of
    their tails. `TieFree` requires that distinct assigned arcs have tails with distinct `F_l`
    values. This is the paper's "if two tails have the same value, the interface is invalid".
    `chain` is `(l, a_0, b_0), ..., (l, a_q, b_q)` with `e_s = (b_{s-1}, a_s)`.

18. **(V2)** is stated as `Nodup` of the multiset of all ends of all sub-demands, where a
    sub-demand `(l, a, a)` contributes `a` once. This is exactly "pairwise distinct, except that
    `a_s = b_s` is allowed within one sub-demand". **(V3)** counts the sub-demands on each side
    with multiplicity.

19. **lem:sound** is stated for every `U` and every `Π` whose ends lie in `U`. This is more
    general than "for every entry".

## Complexity (Complexity.lean)

20. **No machine model.** lem:time is stated as cardinality bounds.
    - The objects counted: entries (`card_entries_le`), splits (`card_splits_le`), and
      interfaces (`card_interfaces_le`).
    - Split-rule work: `splitWork` is the number of (entry, split, interface) triples. Each
      triple takes time that depends only on `k`. `splitWork_le` bounds it by
      `f₁(k) n^{2(k-1) + 2P(k) + 1 + 2(3k-4)}`, and `exponent_eq` shows that this exponent is
      `6k² - 4k - 1`.
    - Leaf-rule work: `leafWork` adds up the sizes `n^{|Π|} · n` of the pebble-game graphs.
    - Final bound: `lem_time` gives `splitWork + leafWork ≤ f(k) · n^{6k²-4k-1}`.
    - Not counted: the preprocessing (Dijkstra, sorting, `O(k(m + n log n))`).

## Not formalized

- cor:undirected (the reduction from undirected to directed graphs).
- prop:arcdisjoint and prop:edgedisjoint (section "Remarks and open problems").
- The output of a solution (unfolding stored choices).
- The removal of parallel arcs (item 1).
