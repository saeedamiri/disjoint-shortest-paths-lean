/-
The averaging lemma (lem:averaging) and the good level (cor:goodlevel), in a discrete form
without integrals (see `DEVIATIONS.md`).

Paper: "Directed k Disjoint Shortest Paths Is Polynomial for Every Fixed k" (Saeed Amiri),
Section "The cut hierarchy", subsection "The averaging lemma".
-/
import DSPP.Hierarchy

open Classical

namespace DSPP

/-- The measure step of cor:goodlevel, without measure theory.  A finite family of open
intervals (given by unordered end points `a s`, `b s`) of total length less than
`(c + 1) (hi - lo)` leaves a point of `(lo, hi)`, outside any given finite set, that lies in at
most `c` of the intervals. -/
theorem exists_low_count {ι : Type*} (S : Finset ι) (a b : ι → ℝ) (lo hi : ℝ) (c : ℕ)
    (bad : Finset ℝ) (hlt : lo < hi)
    (hsum : ∑ s ∈ S, |b s - a s| < (c + 1) * (hi - lo)) :
    ∃ x, lo < x ∧ x < hi ∧ x ∉ bad ∧
      (S.filter fun s => min (a s) (b s) < x ∧ x < max (a s) (b s)).card ≤ c := by
  sorry

variable {k : ℕ} [NeZero k] {V : Type*} [Fintype V] [DecidableEq V]

namespace Instance

variable (G : Instance V k)

/-- lem:averaging (discrete form).  Let `C` be a cell of width `E > 0` and `X_{1j}` a widest
star coordinate.  Then, for all generic `λ` outside a finite set, `N_C(λ)` is the number of
intervals of a finite family `(a s, b s)` that contain `λ` (a step function), and the total
length of the family (the integral of the step function) is at most `(3k - 4) E`. -/
theorem lem_averaging (Rs : Fin k → List V) (hRs : ∀ l, G.IsDPath l (Rs l))
    (C : Cell k) (j : StarIdx k) (hE : 0 < C.width) (hj : C.ext 0 j.1 = C.width) :
    ∃ (N : ℕ) (a b : Fin N → ℝ) (bad : Finset ℝ),
      ∑ s, |b s - a s| ≤ (3 * (k : ℝ) - 4) * C.width ∧
      ∀ lam, G.IsGeneric j lam → lam ∉ bad →
        G.crossNum Rs C j lam =
          (Finset.univ.filter fun s => min (a s) (b s) < lam ∧ lam < max (a s) (b s)).card := by
  sorry

/-- cor:goodlevel.  In the situation of lem:averaging there is a good level: a generic `λ` with
`m + θE ≤ λ ≤ M - θE` and `N_C(λ) ≤ 3k - 4`, where `θ = 1/(6k)` and `[m, M] = [a_j, b_j]` is
the range of `X_{1j}` on `C`. -/
theorem cor_goodlevel (Rs : Fin k → List V) (hRs : ∀ l, G.IsDPath l (Rs l))
    (C : Cell k) (j : StarIdx k) (hE : 0 < C.width) (hj : C.ext 0 j.1 = C.width) :
    ∃ lam, G.IsGoodLevel Rs C j lam := by
  sorry

end Instance

end DSPP
