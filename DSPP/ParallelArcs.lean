/-
Removing parallel arcs (text after lem:Di).

Paper: "Directed k Disjoint Shortest Paths Is Polynomial for Every Fixed k" (Saeed Amiri),
Section "Preliminaries", text after lem:Di: "We may also assume that `G` has no parallel arcs:
of several arcs from `u` to `v` keep one of minimum length; this changes no distance, and a
solution using a deleted arc can use the kept one instead."

A directed multigraph (`MGraph.ofArcs`) becomes an `Instance` by keeping, for every ordered
pair `(u, v)` with `u ≠ v`, one arc of minimum length (`simpleInst`).  Its vertex-disjoint
solutions correspond to those of the multigraph (`parallel_arcs`), so `thm_main` applies to
multigraph inputs (`thm_main_multigraph`).  A solution of `simpleInst` gives one of the
multigraph explicitly (`liftSol`).
-/
import DSPP.Multigraph
import DSPP.Main

open Classical

namespace DSPP

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] {k : ℕ}
variable (src tgt : E → V) (len : E → ℝ) (hpos : ∀ e, 0 < len e)

/-- The arcs from `u` to `v`. -/
noncomputable def arcsFromTo (u v : V) : Finset E :=
  Finset.univ.filter fun e => src e = u ∧ tgt e = v

/-- The length of a shortest arc from `u` to `v` (`1` if there is none; never used then). -/
noncomputable def minLen (u v : V) : ℝ :=
  if h : (arcsFromTo src tgt u v).Nonempty then (arcsFromTo src tgt u v).inf' h len else 1

theorem minLen_le {e : E} : minLen src tgt len (src e) (tgt e) ≤ len e := by
  have h : e ∈ arcsFromTo src tgt (src e) (tgt e) := by simp [arcsFromTo]
  rw [minLen, dif_pos ⟨e, h⟩]
  exact Finset.inf'_le _ h

theorem exists_minLen {u v : V} (h : ∃ e, src e = u ∧ tgt e = v) :
    ∃ e, src e = u ∧ tgt e = v ∧ len e = minLen src tgt len u v := by
  obtain ⟨e, he⟩ := h
  have hne : (arcsFromTo src tgt u v).Nonempty := ⟨e, by simp [arcsFromTo, he]⟩
  obtain ⟨f, hf, hfl⟩ := Finset.exists_mem_eq_inf' hne len
  have hf' : src f = u ∧ tgt f = v := by simpa [arcsFromTo] using hf
  refine ⟨f, hf'.1, hf'.2, ?_⟩
  rw [minLen, dif_pos hne, hfl]

/-- The instance without parallel arcs: an arc `(u, v)` for `u ≠ v` whenever the multigraph has
an arc from `u` to `v`, of the minimum length of these arcs. -/
noncomputable def simpleInst (s t : Fin k → V) (hinj : Function.Injective (Sum.elim s t))
    (hk : 2 ≤ k) : Instance V k where
  arc u v := u ≠ v ∧ ∃ e, src e = u ∧ tgt e = v
  len := minLen src tgt len
  len_pos u v h := by
    obtain ⟨e, he1, he2, hl⟩ := exists_minLen src tgt len h.2
    rw [← hl]; exact hpos e
  s := s
  t := t
  terminals_injective := hinj
  two_le_k := hk

/-- The arcs of a walk `a, d, …` of the instance without parallel arcs: for consecutive vertices
`u`, `v` an arc from `u` to `v` of minimum length (the walk stops where there is none). -/
noncomputable def liftR : V → List V → List (E × V)
  | _, [] => []
  | a, d :: R => if h : ∃ e, src e = a ∧ tgt e = d ∧ len e = minLen src tgt len a d
      then (h.choose, d) :: liftR d R else []

section

variable (s t : Fin k → V) (hinj : Function.Injective (Sum.elim s t)) (hk : 2 ≤ k)

theorem verts_isPath {a b : V} {W : List (E × V)}
    (h : (MGraph.ofArcs src tgt len hpos).IsPath a W b) :
    (simpleInst src tgt len hpos s t hinj hk).IsPath (MGraph.verts a W) a b ∧
      (simpleInst src tgt len hpos s t hinj hk).wlen (MGraph.verts a W) ≤
        (MGraph.ofArcs src tgt len hpos).mlen W := by
  set G := simpleInst src tgt len hpos s t hinj hk
  set M := MGraph.ofArcs src tgt len hpos
  induction W generalizing a with
  | nil =>
    have hab : a = b := h.1
    subst hab
    exact ⟨⟨⟨by simp [MGraph.verts], by simp [MGraph.verts], by simp [MGraph.verts]⟩,
      by simp [MGraph.verts]⟩, by simp [MGraph.verts, G.wlen_singleton]⟩
  | cons x W ih =>
    obtain ⟨⟨⟨-, h1, h2⟩, -⟩, hl⟩ := ih (M.isPath_tail h)
    have hstep : src x.1 = a ∧ tgt x.1 = x.2 := h.1.1
    have hne : a ≠ x.2 := by
      intro he
      exact (List.nodup_cons.1 h.2).1 (he ▸ by simp [MGraph.verts])
    have hv : MGraph.verts x.2 W = x.2 :: W.map Prod.snd := rfl
    rw [MGraph.verts_cons, hv]
    rw [hv] at h1 h2 hl
    refine ⟨⟨⟨by simp, ?_, ?_⟩, h.2⟩, ?_⟩
    · rw [List.getLast?_cons_cons]; exact h1
    · exact List.isChain_cons_cons.2 ⟨⟨hne, x.1, hstep⟩, h2⟩
    · rw [G.wlen_cons_cons, MGraph.mlen_cons]
      have : G.len a x.2 ≤ M.len x.1 := by
        show minLen src tgt len a x.2 ≤ len x.1
        rw [← hstep.1, ← hstep.2]; exact minLen_le src tgt len
      linarith

/-- A path `R` of `simpleInst` from `a` gives the path `liftR a R.tail` of the multigraph with the
same vertices and the same length. -/
theorem liftR_isPath : ∀ (R : List V) (a b : V),
    (simpleInst src tgt len hpos s t hinj hk).IsPath R a b →
    (MGraph.ofArcs src tgt len hpos).IsPath a (liftR src tgt len a R.tail) b ∧
      MGraph.verts a (liftR src tgt len a R.tail) = R ∧
      (MGraph.ofArcs src tgt len hpos).mlen (liftR src tgt len a R.tail) =
        (simpleInst src tgt len hpos s t hinj hk).wlen R := by
  set G := simpleInst src tgt len hpos s t hinj hk
  intro R
  induction R with
  | nil => intro a b h; simp [Instance.IsPath, Instance.IsWalk] at h
  | cons c R ih =>
    intro a b ⟨⟨hh, hl, hc⟩, hnd⟩
    have hca : c = a := by simpa using hh
    subst hca
    cases R with
    | nil =>
      have : c = b := by simpa using hl
      subst this
      exact ⟨⟨by simp [liftR], by simp [MGraph.verts, liftR]⟩, by simp [MGraph.verts, liftR],
        by simp [liftR, G.wlen_singleton]⟩
    | cons d R =>
      rw [List.isChain_cons_cons] at hc
      obtain ⟨hW, hWv, hWl⟩ := ih d b ⟨⟨by simp, by simpa using hl, hc.2⟩,
        (List.nodup_cons.1 hnd).2⟩
      have hex := exists_minLen src tgt len hc.1.2
      simp only [List.tail_cons] at hW hWv hWl
      simp only [List.tail_cons, liftR, dif_pos hex]
      obtain ⟨he1, he2, hel⟩ := hex.choose_spec
      refine ⟨⟨⟨⟨he1, he2⟩, hW.1⟩, ?_⟩, ?_, ?_⟩
      · rw [MGraph.verts_cons]; simp only at hWv ⊢; rw [hWv]; exact hnd
      · rw [MGraph.verts_cons]; simp only at hWv ⊢; rw [hWv]
      · rw [MGraph.mlen_cons, G.wlen_cons_cons, hWl]
        simp only [MGraph.ofArcs] at hel ⊢
        rw [hel]; rfl

theorem lift_isPath (R : List V) (a b : V)
    (h : (simpleInst src tgt len hpos s t hinj hk).IsPath R a b) :
    ∃ W, (MGraph.ofArcs src tgt len hpos).IsPath a W b ∧ MGraph.verts a W = R ∧
      (MGraph.ofArcs src tgt len hpos).mlen W = (simpleInst src tgt len hpos s t hinj hk).wlen R :=
  ⟨_, liftR_isPath src tgt len hpos s t hinj hk R a b h⟩

/-- The paths of the multigraph read off paths `R` of `simpleInst` (`liftR`). -/
noncomputable def liftSol (R : Fin k → List V) : Fin k → List (E × V) :=
  fun i => liftR src tgt len (s i) (R i).tail

/-- `liftSol` maps every solution of `simpleInst` to pairwise vertex-disjoint shortest paths of
the multigraph. -/
theorem isVertexSolution_liftSol {R : Fin k → List V}
    (hR : (simpleInst src tgt len hpos s t hinj hk).IsSolution R) :
    (MGraph.ofArcs src tgt len hpos).IsVertexSolution s t (liftSol src tgt len s R) := by
  obtain ⟨hR, hdis⟩ := hR
  have hW := fun i => liftR_isPath src tgt len hpos s t hinj hk (R i) _ _ (hR i).1
  refine ⟨fun i => ⟨(hW i).1, fun W' hW' => ?_⟩, ?_⟩
  · obtain ⟨h1, h2⟩ := verts_isPath src tgt len hpos s t hinj hk hW'
    have h3 := (hR i).2 _ h1
    have h4 : (MGraph.ofArcs src tgt len hpos).mlen (liftSol src tgt len s R i) =
        (simpleInst src tgt len hpos s t hinj hk).wlen (R i) := (hW i).2.2
    linarith
  · intro i j hij v hv hv'
    have hi : MGraph.verts (s i) (liftSol src tgt len s R i) = R i := (hW i).2.1
    have hj : MGraph.verts (s j) (liftSol src tgt len s R j) = R j := (hW j).2.1
    rw [hi] at hv
    rw [hj] at hv'
    exact hdis i j hij v hv hv'

/-- Text after lem:Di (removal of parallel arcs).  A directed multigraph with positive lengths
and `2k` distinct terminals has pairwise vertex-disjoint shortest paths iff the instance that
keeps one arc of minimum length per ordered pair has them. -/
theorem parallel_arcs :
    (MGraph.ofArcs src tgt len hpos).HasVertexSolution s t ↔
      (simpleInst src tgt len hpos s t hinj hk).HasSolution := by
  set G := simpleInst src tgt len hpos s t hinj hk
  set M := MGraph.ofArcs src tgt len hpos
  constructor
  · rintro ⟨P, hP, hdis⟩
    refine ⟨fun i => MGraph.verts (s i) (P i), fun i => ⟨(verts_isPath src tgt len hpos s t
      hinj hk (hP i).1).1, fun R hR => ?_⟩, hdis⟩
    obtain ⟨W, hW, -, hWl⟩ := lift_isPath src tgt len hpos s t hinj hk R _ _ hR
    have h1 := (verts_isPath src tgt len hpos s t hinj hk (hP i).1).2
    have h2 := (hP i).2 W hW
    show G.wlen _ ≤ G.wlen R
    linarith
  · rintro ⟨R, hR⟩
    exact ⟨_, isVertexSolution_liftSol src tgt len hpos s t hinj hk hR⟩

end

/-- thm:main for multigraph inputs: the guillotine table on the instance without parallel arcs
decides the vertex-disjoint problem on a directed multigraph, within the bound of `thm_main`. -/
theorem thm_main_multigraph :
    ∃ f : ℕ → ℕ, ∀ (k : ℕ) [NeZero k] (V E : Type) [Fintype V] [DecidableEq V] [Fintype E]
      (src tgt : E → V) (len : E → ℝ) (hpos : ∀ e, 0 < len e) (s t : Fin k → V)
      (hinj : Function.Injective (Sum.elim s t)) (hk : 2 ≤ k),
      ((simpleInst src tgt len hpos s t hinj hk).Tab Finset.univ
          (simpleInst src tgt len hpos s t hinj hk).Pi0 ↔
        (MGraph.ofArcs src tgt len hpos).HasVertexSolution s t) ∧
      (simpleInst src tgt len hpos s t hinj hk).splitWork +
          (simpleInst src tgt len hpos s t hinj hk).leafWork ≤
        f k * Fintype.card V ^ (6 * k ^ 2 - 4 * k - 1) := by
  obtain ⟨hcor, ⟨f, hf⟩, -⟩ := thm_main
  refine ⟨f, fun k _ V E _ _ _ src tgt len hpos s t hinj hk => ⟨?_, hf k V _⟩⟩
  rw [hcor k V _]
  exact (parallel_arcs src tgt len hpos s t hinj hk).symm

end DSPP
