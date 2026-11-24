# Deviations from the paper

Paper: "Directed k Disjoint Shortest Paths Is Polynomial for Every Fixed k" (Saeed Amiri).
Labels below are the paper's LaTeX labels.

Every entry gives the paper's form, the Lean form, and why the Lean form is equivalent or
sufficient. The main theorem (`DSPP.thm_main`) and the table (`Instance.Tab`) follow the paper.

## Modelling choices (Basic.lean, ShortestDAG.lean, Potentials.lean)

1. **No parallel arcs.** The paper allows parallel arcs and then removes them without loss of
   generality (text after lem:Di). In Lean, arcs are a relation `arc : V → V → Prop` with
   lengths `len : V → V → ℝ`, so there are no parallel arcs from the start. This is the
   paper's normalized instance. The reduction step is formalized separately (item 23).

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
   assume `[NeZero k]`.
   - The fields of `Instance`: `two_le_k` (`k ≥ 2`), `terminals_injective` (the `2k`
     terminals are pairwise distinct) and `len_pos` (lengths are positive on arcs).
   - Consequence: `thm_main` says nothing about `k = 1`, which is the single-pair
     shortest-path problem.

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
    - Paths: `lem_termination` is stated for arbitrary lists `Rs`, without the
      `D_l`-path hypothesis. This is intentional. The argument uses only the widths and the
      position of the levels, and a cell with no good level has no step.

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
    general than "for every entry". **lem:complete** is stated as in the paper:
    `HasSolution → Tab V Π_0`.

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

21. **cor:undirected.** An undirected instance is an `Instance` whose arc relation and
    lengths are symmetric. Each edge `uv` becomes the arcs `(u,v)` and `(v,u)` of the same
    length, which is the paper's reduction. Vertex-disjoint shortest paths are the same in
    both views. `cor_undirected` is `thm_main` restricted to these instances.

## Multigraphs and the remarks (Multigraph.lean, ParallelArcs.lean, LineGraph.lean, Trim.lean, EdgeDisjoint.lean, EdgeDisjointCor.lean)

22. **Multigraphs.** The paper allows parallel arcs and edges in the input.
    - Lean: `MGraph V E` has a set `E` of arcs or edges and a relation `step u e w` (the arc or
      edge `e` leads from `u` to `w`). `ofArcs src tgt` is a digraph; `ofEdges fst snd` is an
      undirected graph, in which an edge can be used both ways.
    - A walk from `a` is a list of pairs (arc or edge, next vertex), so parallel arcs are told
      apart. A path is a walk with distinct vertices. `IsShortestPath` compares against all
      paths.
    - `HasEdgeSolution` asks for pairwise arc- or edge-disjoint shortest paths;
      `HasVertexSolution` asks for pairwise vertex-disjoint ones.

23. **Removing parallel arcs (text after lem:Di).**
    - Lean: `simpleInst` keeps, for each ordered pair `(u, v)` with `u ≠ v` joined by some arc,
      one arc of minimum length. Loops are dropped; a path never uses one.
    - `parallel_arcs`: the multigraph has vertex-disjoint shortest paths iff `simpleInst` has
      a solution. `thm_main_multigraph` is `thm_main` for multigraph inputs.
    - `liftSol` maps a solution of `simpleInst` to one of the multigraph. Between consecutive
      vertices it takes an arc of minimum length (`liftR`). `isVertexSolution_liftSol` proves
      that the result is a solution.

24. **prop:arcdisjoint and prop:edgedisjoint.**
    - Paper: the line digraph `L` has the arcs (edges) of `G` as vertices, plus a new source
      and a new target per pair.
    - Lean: `LineData` builds `L` on `E ⊕ (Fin k ⊕ Fin k)`. `arcLine` is the directed form;
      `edgeLine` joins two edges of an undirected graph when they share an end.
      `prop_arcdisjoint` and `prop_edgedisjoint` give the equivalence and the vertex count
      `|E| + 2k`.
    - Hypotheses: `k ≥ 2`, because `Instance` requires it, and `s_i ≠ t_i` for every `i`, as in
      cor:edgedisjoint.
    - Each proposition also gives the map back. Every solution `Q` of `L` yields `k` disjoint
      shortest paths of `G`, namely `LineData.backSol G s t Q`. For each `i`, `backSol` takes a
      path of `G` that uses only the arcs or edges visited by `Q i` (`pathIn`). It picks among
      the finitely many such paths, not from `HasEdgeSolution`.
    - "`L` is acyclic if `G` is": `prop_arcdisjoint_acyclic`. `MGraph.Acyclic` says that every
      closed walk is empty. `Instance.Acyclic` says that no vertex reaches itself along one or
      more arcs (`Relation.TransGen`). The proof follows the paper: a closed walk of `L` through
      `x_a` gives a closed walk of `G` through the tail of `a`, and the new sources and targets
      lie on no closed walk.

25. **cor:edgedisjoint.**
    - Paper: keep at most `k` arcs (edges) of minimum length between any two vertices, then use
      the propositions and thm:main.
    - Lean: `arcKept` and `edgeKept` keep the `k` shortest arcs (edges) per ordered (unordered)
      pair, and delete loops in both cases. `card_arcKept_le` gives `k·n(n-1)`;
      `card_edgeKept_le` gives `k·C(n,2)`.
    - `cor_edgedisjoint` gives the equivalence, the size `≤ k n² + 2k` of `L`, and the work
      bounds `f(k)·N^{6k²-4k-1}` (with `N` the size of `L`) and `g(k)·n^{2(6k²-4k-1)}`.
    - Terminals of different pairs may coincide: `cor_edgedisjoint` has no injectivity
      hypothesis on the terminals.
    - Hypotheses: `s_i ≠ t_i` for every `i`, as in the statement of cor:edgedisjoint, and
      `k ≥ 2`, because `Instance` requires it (item 4). The paper says "for every fixed `k`";
      the cases `k ≤ 1` are a single shortest path or nothing. Pairs with `s_i = t_i` are not
      claimed by the paper.
    - "Find one": `arcBack` (`edgeBack`) maps a solution of the reduced instance to `k`
      disjoint shortest paths of `G`. It applies `LineData.backSol` on the trimmed graph and
      reads the arcs (edges) as arcs (edges) of `G` (`isEdgeSolution_of_trim`).
      `cor_edgedisjoint_solution`: if the root entry is true, then `arcBack` (`edgeBack`) of
      the table's `solution` is a solution of `G`.

## Output of a solution (Extraction.lean)

26. **Reading the paths off the table.**
    - Paper: the table decides the problem; a solution is found by back-tracking.
    - Lean: `extract` follows the proof of lem:sound by recursion on `|U|`. At a split entry it
      picks a split and a valid interface whose two sub-entries are true, and joins the paths
      of the sub-entries along the chains of the interface (`joinPaths`). At a leaf it picks a
      winning play of the pebble game, and the paths are the pebble trajectories
      (`leafPaths`).
    - The picks are among the table's own finitely many candidates and plays. No step picks
      from `HasSolution`. `extract` is `noncomputable` because the picks use choice.
    - `extract_isSolution`: if the root entry is true, `solution` is a solution.
      `solution_spec`: `HasSolution ↔ IsSolution solution`.

## Routes through prescribed vertices (Waypoints.lean)

27. **Routes.** Paper: a path, cycle or walk through `w_0, …, w_ℓ` in this order.
    - Lean: a route is given by its segments `R i`, a walk from `w i` to `w (i+1)`
      (`IsSegs`). The route is the concatenation `catW R`, and `isWalk_catW` shows it is a walk
      from `w 0` to `w ℓ`. A walk passes through the waypoints in order exactly when it splits
      into such segments.
    - Kind (i), `IsPathRoute`: the vertices of `catW R` are distinct.
    - Kind (ii), `IsCycleRoute`: `w ℓ = w 0`, the vertices of the closed walk are distinct,
      and its arcs or edges are distinct. This is a cycle. In an undirected graph with `ℓ = 2`,
      the walk from `w 0` to `w 1` and back along the same edge has distinct vertices but not
      distinct edges, so it is not a cycle route (`not_isCycleRoute_back`).
    - The reduction uses the fact that distinct vertices force distinct arcs or edges. This
      holds in every digraph (`ofArcs_cycle_hE`). In an undirected graph it holds for
      `ℓ ≥ 3` (`ofEdges_cycle_hE`). So `cor_waypoints` assumes `ℓ ≥ 3` for undirected cycles,
      as the paper does, and the proof uses this hypothesis.
    - Kind (iii), `IsTrailRoute`: the arcs or edges of `catW R` are distinct.

28. **Distance in a multigraph.** `MGraph.dist a b` is the infimum of the lengths of the paths
    from `a` to `b`, and `0` if there is none. `L` is `wayLen w`. The paper's proof assumes `L` finite.
    Lean adds no such hypothesis: if some `w (i+1)` cannot be reached from `w i`, no route
    exists and both sides of each equivalence are false.

29. **The split graph `G'`.**
    - Paper: replace every `w ∈ W` by `w⁻` (arcs in) and `w⁺` (arcs out); `G'` has at most
      `n + ℓ` vertices.
    - Lean: `splitG` lives on `V ⊕ V`, with `w⁻ = inl w` and `w⁺ = inr w` for `w ∈ W`, and
      `inl w` for both otherwise. It has `2n` vertices, some isolated. The work bound becomes
      `f(ℓ)·(2n)^{6ℓ²-4ℓ-1}`, which is `f(ℓ)·2^{6ℓ²-4ℓ-1}·n^{6ℓ²-4ℓ-1}`: same exponent, and the
      constant goes into `f`.
    - An undirected graph enters through both orientations of every edge, as in the paper.
      Lean uses an arc presentation `σ τ π ρ`: arcs `E` for a digraph, `E ⊕ E` for an undirected
      graph.
    - The distance check: the paper answers "no" if `d'(w_{i-1}⁺, w_i⁻) > d(w_{i-1}, w_i)` for
      some `i`. Lean's `splitCheck` is `d' ≤ d` for every `i`. This is the negation of the
      paper's test, because a path of `G'` maps to a walk of `G` of the same length, so
      `d' ≥ d` whenever `w_i⁻` is reachable from `w_{i-1}⁺`.
    - If `w_i⁻` is not reachable in `G'`, then `d' = 0` by convention and `splitCheck` can pass
      where the paper answers "no". Then `G'` has no path for the pair `i`, so the table rejects,
      and the equivalence still holds.

30. **cor:waypoints.** `cor_waypoints` states, for digraphs and undirected graphs:
    - the lower bound `L ≤` the length of every route of every kind (`wayLen_le`);
    - for (i) and (ii): a route of length `L` exists iff `splitCheck` holds and the table of
      thm:main accepts on `G'`, with work at most `f(ℓ)·n^{6ℓ²-4ℓ-1}`;
    - for (iii): a route of length `L` exists iff the table of cor:edgedisjoint accepts for the
      pairs `(w_{i-1}, w_i)`, with work at most `g(ℓ)·n^{2(6ℓ²-4ℓ-1)}`.
    - The `O(m)` preprocessing is not modelled (item 20).
    - "Find one": the route is read off the table's own `solution`. For (i) and (ii), `liftSol`
      turns the paths of the instance into paths of `G'`, and `projW` reads them in `G`
      (`splitRoute`, giving `arcPathRoute`, `arcCycleRoute`, `edgePathRoute` and
      `edgeCycleRoute`). For (iii), `arcBack` (`edgeBack`) maps the solution of
      cor:edgedisjoint back (`arcTrailRoute`, `edgeTrailRoute`). `cor_waypoints_route`: if the
      check passes and the table accepts, the route has the required kind and length `L`.

## Not formalized

- A machine model for the preprocessing (Dijkstra, sorting, `O(k(m + n log n))`), for the
  `O(m)` trimming of cor:edgedisjoint and cor:waypoints, and for the distance check
  `splitCheck` of cor:waypoints. These steps are outside the work bounds, which count only the
  work of the table. Item 20 states the work as counts.

## Not claimed by the paper

- cor:edgedisjoint for pairs with `s_i = t_i`. The paper's statement assumes `s_i ≠ t_i` for
  every `i`, and so does Lean. Terminals of different pairs may coincide in both (item 25).
