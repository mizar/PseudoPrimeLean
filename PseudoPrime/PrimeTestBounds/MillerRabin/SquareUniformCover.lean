/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.SquareUniformCell

/-! # Contiguous coefficient coverage for prime squares -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Check that consecutive coefficient cells cover the interval from `lo` through `hi`.
Each cell must pass its own arithmetic check and overlap the currently covered endpoint;
the recursion ends once a cell reaches `hi`. -/
def squareUniformCoverCheck (lo hi : ℚ) : List SquareUniformCell → Bool
  | [] => false
  | c :: cs =>
    (c.check && decide (c.lo ≤ lo ∧ lo ≤ c.hi)) &&
      (decide (hi ≤ c.hi) || squareUniformCoverCheck c.hi hi cs)

/-- Under RH, a successful contiguous cell check gives the coefficient `371/1000`
rejecting-prime bound for odd prime squares whose logarithm lies in the covered interval.
Induction selects the first cell containing the logarithm and applies its witness theorem. -/
theorem squareUniformCoverCheck_sound {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpow : n = p ^ 2) (hRH : RiemannHypothesis) (cells : List SquareUniformCell)
    (lo hi : ℚ) (hcheck : squareUniformCoverCheck lo hi cells = true) (hlo : (lo : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (hi : ℝ)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (371 / 1000 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  induction cells generalizing lo with
  | nil => simp only [squareUniformCoverCheck, Bool.false_eq_true] at hcheck
  | cons c cs
    ih =>
    have hc :
      ((c.check && decide (c.lo ≤ lo ∧ lo ≤ c.hi)) &&
          (decide (hi ≤ c.hi) || squareUniformCoverCheck c.hi hi cs)) =
        true := by
      simpa only [squareUniformCoverCheck] using hcheck
    have hparts := Bool.and_eq_true_iff.mp hc
    have hleft := Bool.and_eq_true_iff.mp hparts.1
    have hadj : c.lo ≤ lo ∧ lo ≤ c.hi := of_decide_eq_true hleft.2
    by_cases hcell : Real.log n ≤ (c.hi : ℝ)
    · exact
        c.sound hn ho hp hp2 hpow hRH hleft.1 (((Rat.cast_le (K := ℝ)).mpr hadj.1).trans hlo) hcell
    · have hnot : ¬hi ≤ c.hi := by
        intro h
        exact hcell (hhi.trans ((Rat.cast_le (K := ℝ)).mpr h))
      have hrest : squareUniformCoverCheck c.hi hi cs = true := by
        rcases Bool.or_eq_true_iff.mp hparts.2 with hend | hnext
        · exact (hnot (of_decide_eq_true hend)).elim
        · exact hnext
      exact ih c.hi hrest (le_of_lt (lt_of_not_ge hcell))

end PseudoPrime.PrimeTestBounds.MillerRabin
