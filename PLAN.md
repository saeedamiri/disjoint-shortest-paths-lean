# Formalization plan

Paper: "Directed k Disjoint Shortest Paths Is Polynomial for Every Fixed k" (Saeed Amiri).

Target: a Lean proof of `DSPP.thm_main` with no `sorry` and no axioms beyond `propext`,
`Classical.choice` and `Quot.sound`. The theorem has two parts:

- **Correctness.** The guillotine table `Instance.Tab` (def:table) is true at the root iff a
  solution exists (cor:correct).
- **Size.** The work of the table is at most `f(k) · n^{6k²-4k-1}` (lem:time).

`lake build` (inside `lean/`) succeeds. Every remaining `sorry` is in a proof; no definition
contains one. Run `#print axioms` on any definition to check this.

## Rules for builders

- **Frozen.** All definitions and all theorem statements below are frozen. Change one only
  through the router: a change to a statement changes the contract with the other packages.
- **Write only in your own files.** Add helper lemmas in the files your package owns, or in a
  new file `DSPP/<Package>/*.lean` that only your files import. Never add helper lemmas to a
  file that another package owns.
- **Using other packages.** Any statement of another package may be used as a black box, even
  while it still has a `sorry`.
- **Checks before handing over.** `lake build` passes, no new `axiom` and no `admit`, and
  `#print axioms` on your theorems shows only `sorryAx` coming from other packages.

## Label table

Status: **proved** (no `sorry` in the proof itself, but it may use sorried lemmas), **sorry**,
or **def** (a definition).

| Paper label | Lean name | File | Status |
|---|---|---|---|
| instance, paths, solution | `Instance`, `IsWalk`, `IsPath`, `wlen`, `Reach`, `dist`, `d`, `IsShortestPath`, `IsSolution`, `HasSolution` | Basic | def |
| (basic distance facts) | `wlen_nonneg`, `dist_le_wlen`, `dist_nonneg`, `dist_le_dist_add_len`, `dist_le_len_add_dist`, `dist_triangle`, `exists_path_of_walk`, `dist_eq_min_path`, `isShortestPath_iff` | Basic | sorry |
| def:Di | `inD`, `IsDPath` | ShortestDAG | def |
| lem:Di (a), (b), (c) | `lem_Di_a`, `lem_Di_b`, `lem_Di_c` | ShortestDAG | sorry |
| def:potentials | `F`, `pt`, `Xv`, `X`, `SameClass`, `StarIdx` | Potentials | def |
| lem:W0 | `lem_W0` | Potentials | sorry |
| lem:W12 | `lem_W1`, `lem_W2` | Potentials | proved (from `lem_W0`) |
| point classes and star coordinates (text) | `sameClass_iff_star` | Potentials | proved |
| lem:classpiece | `lem_classpiece` | Potentials | sorry |
| def:cell | `Cell`, `Cell.carrier`, `Cell.ext`, `Cell.width`, `Cell.lower`, `Cell.upper`, `cellVerts`, `starX` | Cells | def |
| lem:extent (a), (b), (c) | `Cell.lem_extent_a`, `Cell.lem_extent_b`, `Cell.lem_extent_c` | Cells | sorry |
| generic levels | `IsGeneric`, `nonGeneric_finite` | Crossing | def / proved |
| def:N | `crossNum` (arc by arc), `crossPt`, `segCross`; paper form `curve`, `curveCount` | Crossing | def |
| def:N, the two forms agree | `crossNum_eq_curveCount` | Crossing | sorry (not on the main path) |
| pieces | `pieces`, `numPieces` | Crossing, Hierarchy | def |
| `P(k)` | `P`, `P_eq` | Hierarchy | def / proved |
| def:hierarchy | `CutTree`, `CutTree.nodes`, `IsHierarchy`, `cut_of_mem_nodes` | Hierarchy | def / proved |
| def:construction | `rootCell`, `theta`, `IsGoodLevel`, `ConstrCut`, `ConstrStep`, `IsConstructionTree`, `AtMostOneClass`, `crossArcCount` | Hierarchy | def |
| lem:averaging | `lem_averaging` | Averaging | sorry |
| (measure step) | `exists_low_count` | Averaging | sorry |
| cor:goodlevel | `cor_goodlevel` | Averaging | sorry |
| lem:termination | `lem_termination` | Termination | sorry |
| def:construction (text) | `width_pos_of_not_atMostOneClass`, `exists_constrCut`, `exists_constructionTree` | Termination | sorry |
| def:construction (text) | `isHierarchy_of_isConstructionTree` | Termination | proved |
| lem:pieces | `lem_pieces` | Pieces | sorry |
| thm:hierarchy | `thm_hierarchy` | HierarchyThm | sorry |
| cor:crossarcs | `crossArcCount_le_crossNum` / `cor_crossarcs` | HierarchyThm | sorry / proved |
| def:box | `Lam`, `boxOf`, `IsBoxSet`, `boxSets`, `pointClass`, `IsPointClass` | Boxes | def |
| lem:box (a)–(e) | `lem_box_a` … `lem_box_e` | Boxes | sorry |
| def:S, demands | `Demand`, `IsDemandPath`, `Sem`, `Pi0` | Demands | def |
| `S(V, Π_0)` iff a solution exists (text) | `sem_root_iff` | Demands | sorry |
| lem:pebbling (game) | `Pebble.Move`, `Pebble.Wins`, `Pebble.DisjointPaths` | Pebbling | def |
| lem:pebbling (Fortune–Hopcroft–Wyllie) | `Pebble.fhw` | Pebbling | sorry |
| lem:pebbling (size of the game) | `Pebble.card_states` / `Pebble.card_moves_le` | Pebbling | proved / sorry |
| def:table | `key`, `pebbleWins`, `DistinctLabels`, `leafRule`, `IsSplit`, `splits`, `Uminus`, `Uplus`, `candPairs`, `interfaces`, `assigned`, `TieFree`, `sortedArcs`, `chain`, `allSub`, `demandEnds`, `subMinus`, `subPlus`, `PiMinus`, `PiPlus`, `Valid`, `Tab`, `IsEntry` | Table | def |
| def:table (recursion) | `Tab_eq`, `card_Uminus_lt`, `card_Uplus_lt`, `key_injective` | Table | proved |
| lem:pebbling | `lem_pebbling` | Leaf | sorry |
| lem:sound | `lem_sound` | Correctness | sorry |
| lem:complete | `lem_complete` | Correctness | sorry |
| cor:correct | `cor_correct` | Correctness | proved (from sound, complete, `sem_root_iff`) |
| root entry | `isEntry_root` | Correctness | sorry |
| lem:time | `entries`, `splitWork`, `leafWork` | Complexity | def |
| lem:time | `card_entries_le`, `card_splits_le`, `card_interfaces_le`, `splitWork_le`, `leafWork_le`, `lem_time` | Complexity | sorry |
| lem:time (exponent) | `exponent_eq` | Complexity | proved |
| thm:main | `thm_main` | Main | proved (from `cor_correct`, `lem_time`) |

Not formalized (outside the target): cor:undirected, prop:arcdisjoint, prop:edgedisjoint, the
removal of parallel arcs, and the output of a solution. See `DEVIATIONS.md`.

## Dependencies

File import order:
Basic → ShortestDAG → Potentials → Cells → Crossing → Hierarchy → {Averaging → Termination,
Pieces} → HierarchyThm; Hierarchy → Boxes → Demands; Pebbling (independent); {Demands,
Pebbling} → Table → Leaf → Correctness (also imports HierarchyThm); Table → Complexity;
{Correctness, Complexity} → Main.

The proof dependencies on the main path:

```
thm_main ← cor_correct ← lem_sound ← lem_pebbling ← Pebble.fhw, lem_W2 ← lem_W0
                       ← lem_complete ← thm_hierarchy ← exists_constructionTree ← lem_termination,
                       │                │                 exists_constrCut ← cor_goodlevel ← lem_averaging
                       │                │                 (lem_W1, lem_extent), exists_low_count
                       │                ← lem_pieces, isHierarchy_of_isConstructionTree
                       │              ← cor_crossarcs ← crossArcCount_le_crossNum
                       │              ← lem_box_c, lem_box_e, lem_classpiece, lem_Di_b, lem_W0
                       ← sem_root_iff ← lem_Di_b
         ← lem_time ← card_entries_le (lem_box_a), card_splits_le, card_interfaces_le,
                      splitWork_le, leafWork_le, exponent_eq
```

## Work packages

The packages can run in parallel: each owns disjoint files and uses only the frozen
statements of the others.

### WP1: Foundations (standard)

- **Owns:** `Basic.lean`, `ShortestDAG.lean`, `Potentials.lean`, `Cells.lean`,
  `Boxes.lean`, `Demands.lean`.
- **Proves:** the basic distance facts (the shortcut lemma `exists_path_of_walk` is the only one
  that is not routine), `lem_Di_a`, `lem_Di_b`, `lem_Di_c`, `lem_W0`, `lem_classpiece`,
  `lem_extent_a`, `lem_extent_b`, `lem_extent_c`, `lem_box_a` … `lem_box_e`, and
  `sem_root_iff`.
- **Black boxes:** none needed.
- **Notes:**
  - `lem_W0` needs case splits on `Reach`, using the triangle inequalities.
  - `lem_extent_b` needs `sSup`/`sInf` on the images of the carrier. Prove (a) first and
    compute the images exactly.
  - `lem_box_a` is an injection from box sets to bound tuples in `∏ Λ_j²`.

### WP2: Averaging and termination (strong)

- **Owns:** `Averaging.lean`, `Termination.lean`, and `Crossing.lean` (for the optional
  `crossNum_eq_curveCount`).
- **Proves:** `exists_low_count`, `lem_averaging`, `cor_goodlevel`,
  `width_pos_of_not_atMostOneClass`, `lem_termination`, `exists_constrCut`,
  `exists_constructionTree`.
- **Black boxes:** `lem_W1`, `lem_extent_*`.
- **Notes:**
  - `lem_averaging`, the family of intervals: for each path `l` and each arc `q` of `R_l`, the
    parameters `s ∈ [0,1]` with `(1-s)π(v_q) + sπ(v_{q+1}) ∈ C` form a closed interval (`C` is
    convex). Its end values of `X_{1j}` give one interval `(a, b)`.
  - `lem_averaging`, the bound: the three cases `l = 1`, `l = j`, and `l ∉ {1, j}` follow the
    paper. Telescoping along the monotone coordinate `X_{lp}` uses that these sub-intervals
    are ordered along the path.
  - `exists_low_count`: induction on the family, or `MeasureTheory.volume` on `ℝ`.
  - `lem_termination`: the width shrinks by `1-θ` every `k-1` levels, and a non-leaf cell has
    width at least the smallest positive gap `δ`. A natural measure is
    `⌈log(w/δ)/log(1/(1-θ))⌉` together with the number of star coordinates still above
    `(1-θ)w`. Any well-founded argument will do.

### WP3: Pieces and the hierarchy theorem (strong)

- **Owns:** `Pieces.lean`, `HierarchyThm.lean`.
- **Proves:** `lem_pieces`, `crossArcCount_le_crossNum`, `thm_hierarchy`.
- **Black boxes:** `exists_constructionTree`, `isHierarchy_of_isConstructionTree`,
  `lem_extent_*`, `Cell.carrier` convexity (`lem_extent_a`).
- **Notes:**
  - `lem_pieces`, arc-by-arc charging: see `DEVIATIONS.md` item 9.
  - Write the bounds of a cell of the tree as those of the root, each overwritten by the last
    cut of its type. A piece's entering arc goes from outside `C` but inside `C_0` to inside
    `C`, so the point where it enters `C` lies on the level of a last half-space `h` and inside
    `A_h`. The arc therefore straddles `λ_h`, and it is counted by `crossNum Rs A_h j_h λ_h`.
  - Make the injectivity argument per arc position.
  - `thm_hierarchy`: take the construction tree from `rootCell`. (H1) holds by the min/max
    bounds. (H2) holds by `IsGoodLevel`. (H3) holds by `lem_pieces`. (H4) holds by the leaf
    rule of the construction (via `IsConstructionTree` and `nodes`).

### WP4: Pebbling (standard)

- **Owns:** `Pebbling.lean`, `Leaf.lean`.
- **Proves:** `Pebble.fhw`, `Pebble.card_moves_le`, `lem_pebbling`.
- **Black boxes:** `lem_W2`, `key_injective`.
- **Notes:**
  - `fhw` (⇐): induction on the total remaining length of the paths. The pebble that the rule
    selects can advance, because the next vertex on its path is not occupied by another pebble.
  - `fhw` (⇒): follow each pebble's trajectory, which is a path because `key` increases along
    it. For disjointness, use the invariant "every unfinished pebble other than the one moving
    is at a `key`-larger position", as in the paper.
  - `lem_pebbling`: instantiate the general lemma with `ι = {δ // δ ∈ Π}`. The arcs of
    `D_l[U]` increase `F_1` inside a point class (`lem_W2`), and so they increase `key`.

### WP5: Correctness (strong)

- **Owns:** `Correctness.lean`.
- **Proves:** `lem_sound`, `lem_complete`, `isEntry_root`.
- **Black boxes:** `lem_pebbling`, `thm_hierarchy`, `cor_crossarcs`, `lem_box_*`,
  `lem_classpiece`, `lem_W0`, `lem_Di_b`, `sem_root_iff`, `Tab_eq`.
- **Notes:**
  - `lem_sound`: strong induction on `U.card` with `Tab_eq`. Concatenate the sub-paths along
    the chains.
  - `lem_complete`: induction over the hierarchy (`CutTree`) from the leaves. Use
    `Π(C) = {(l, head, last) : pieces of P_l in V(C)}`.
  - `lem_complete`, the main work: show that `PiMinus` and `PiPlus` of the interface built from
    the crossing arcs are `Π(C⁻)` and `Π(C⁺)`. This is a list lemma about `pieces`, `chain`
    and `mergeSort`; budget for it.

### WP6: Complexity (standard)

- **Owns:** `Complexity.lean`.
- **Proves:** `card_entries_le`, `card_splits_le`, `card_interfaces_le`, `splitWork_le`,
  `leafWork_le`, `lem_time`.
- **Black boxes:** `lem_box_a`.
- **Notes:**
  - Use `Finset.card_le_card` against product and powerset Finsets.
  - Use `Σ_{i ≤ c} C(N, i) ≤ (N+1)^c`.
  - The number of point classes is at most `n`.
  - Use `n ≥ 1`, which holds because the terminals exist.

## Suggested order

- **Start in parallel:** WP1, WP2, WP3, WP4 and WP6.
- **WP5** can also start at once on its black boxes; it is the largest package.
- **Done:** when `#print axioms DSPP.thm_main` no longer lists `sorryAx`.
