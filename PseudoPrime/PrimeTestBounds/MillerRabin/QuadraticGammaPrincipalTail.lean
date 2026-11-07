/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaUpperRows

/-! # Explicit principal Gamma tail for the low middle cells -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- At positive scale through 800, the exponential Mangoldt tail starting
at 20001 is at most 1/100. Apply the existing polynomial majorant and the
certified exponential bound at -24. This removes the infinite-tail numerical
premise for the finite principal upper certificates. -/
theorem gamma_principal_tail_20001 {x : ℝ} (hx : 0 < x) (hxb : x ≤ 800) :
    LLS.principalExponentialTailBound x 20001 ≤ 1 / 100 := by
  have ht := LLS.principalExponentialTailBound_le_polynomial hx 20001
  have he : Real.exp (-(20001 : ℝ) / x) ≤ 1 / 10000000000 :=
    (Real.exp_le_exp.mpr ((div_le_iff₀ hx).mpr (by linarith only [hxb]))).trans
      LLS.exp_neg_twenty_four_le
  have hm :=
    mul_le_mul_of_nonneg_right he
      (mul_nonneg (by linarith only [hx] : 0 ≤ x + 1) (by linarith only [hx] : 0 ≤ x + 20001))
  have hp : (x + 1) * (x + 20001) ≤ (801 : ℝ) * 20801 :=
    mul_le_mul (by linarith only [hxb]) (by linarith only [hxb]) (by linarith only [hx])
      (by norm_num only)
  nlinarith only [ht, hm, hp]

/-- For scales between 1 and 800, a finite normalized principal upper cap
through 20000 gives an upper cap plus 1/100 for the actual infinite series.
The square root is at least one, so the unnormalized tail allowance remains
valid after normalization. This supplies the early Gamma-cell comparison. -/
theorem gamma_principal_upper_small {x U : ℝ} (hx : 1 ≤ x) (hxb : x ≤ 800)
    (hU :
      (∑ n ∈ Finset.Ioc (0 : ℕ) 20000,
          Real.exp (-(n : ℝ) / x) * ArithmeticFunction.vonMangoldt n / Real.sqrt x) ≤
        U) :
    (∑' n : ℕ, Real.exp (-(n : ℝ) / x) * ArithmeticFunction.vonMangoldt n / Real.sqrt x) ≤
      U + 1 / 100 := by
  have hx0 := zero_lt_one.trans_le hx
  apply gamma_principal_upper_of_prefix hx0 20000 hU
  have ht := gamma_principal_tail_20001 hx0 hxb
  apply (div_le_iff₀ (Real.sqrt_pos.mpr hx0)).mpr
  exact
    ht.trans
      (le_mul_of_one_le_right (by norm_num only : (0 : ℝ) ≤ 1 / 100) (Real.one_le_sqrt.mpr hx))

end PseudoPrime.PrimeTestBounds.MillerRabin
