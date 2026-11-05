/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.SemiprimeUniformCell

/-! # Contiguous coefficient coverage for semiprimes -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Check that individually valid semiprime coefficient cells overlap and cover the
interval from `lo` through `hi`. The recursion ends when a checked cell reaches `hi`. -/
def semiprimeUniformCoverCheck (lo hi : ℚ) : List SemiprimeUniformCell → Bool
  | [] => false
  | c :: cs =>
    (c.check && decide (c.lo ≤ lo ∧ lo ≤ c.hi)) &&
      (decide (hi ≤ c.hi) || semiprimeUniformCoverCheck c.hi hi cs)

/-- Under GRH, a successful contiguous check gives the `409/1000` rejecting-prime bound
for odd products of distinct primes throughout the interval. Induction selects the first
cell containing the actual logarithmic scale and applies its witness theorem. -/
theorem semiprimeUniformCoverCheck_sound {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (cells : List SemiprimeUniformCell) (lo hi : ℚ)
    (hcheck : semiprimeUniformCoverCheck lo hi cells = true) (hlo : (lo : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (hi : ℝ)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (409 / 1000 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  induction cells generalizing lo with
  | nil => simp only [semiprimeUniformCoverCheck, Bool.false_eq_true] at hcheck
  | cons c cs
    ih =>
    have hc :
      ((c.check && decide (c.lo ≤ lo ∧ lo ≤ c.hi)) &&
          (decide (hi ≤ c.hi) || semiprimeUniformCoverCheck c.hi hi cs)) =
        true := by
      simpa only [semiprimeUniformCoverCheck] using hcheck
    have hparts := Bool.and_eq_true_iff.mp hc
    have hleft := Bool.and_eq_true_iff.mp hparts.1
    have hadj : c.lo ≤ lo ∧ lo ≤ c.hi := of_decide_eq_true hleft.2
    by_cases hcell : Real.log n ≤ (c.hi : ℝ)
    · exact
        c.sound hn ho hp hq hpq hprod hGRH hleft.1 (((Rat.cast_le (K := ℝ)).mpr hadj.1).trans hlo)
          hcell
    · have hnot : ¬hi ≤ c.hi := by
        intro h
        exact hcell (hhi.trans ((Rat.cast_le (K := ℝ)).mpr h))
      have hrest : semiprimeUniformCoverCheck c.hi hi cs = true := by
        rcases Bool.or_eq_true_iff.mp hparts.2 with hend | hnext
        · exact (hnot (of_decide_eq_true hend)).elim
        · exact hnext
      exact ih c.hi hrest (le_of_lt (lt_of_not_ge hcell))

end PseudoPrime.PrimeTestBounds.MillerRabin
