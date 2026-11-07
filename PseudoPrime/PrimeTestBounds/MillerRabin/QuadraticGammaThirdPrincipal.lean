/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaUpperCell2Chunks
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaPrincipalTail

/-! # Principal Gamma upper bound for the third middle cell -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

set_option maxRecDepth 8192 in
/-- The exponential upper endpoints cover every prime-power row through 20000.
The structural check proves all Taylor comparisons with exact list alignment. -/
theorem gamma_third_upper_exp_check :
    gammaUpperListCheck gammaUpperCell2Scale (centerRowsBelow 20000) gammaUpperCell2Exp = true := by
  decide +kernel

/-- The third-cell scale is in the range supported by the tail estimate, and
the supplied positive radius is a lower bound for its square root. -/
theorem gamma_third_upper_scale_check :
    1 ≤ gammaUpperCell2Scale ∧
      gammaUpperCell2Scale ≤ 800 ∧
      0 < gammaUpperCell2Radius ∧ gammaUpperCell2Radius ^ 2 ≤ gammaUpperCell2Scale := by
  decide +kernel

/-- The finite normalized principal sum through 20000 is bounded by the
checked chunk total. The exponential and support checks account for every
prime-power contribution. -/
theorem gamma_third_principal_finite :
    (∑ n ∈ Finset.Ioc (0 : ℕ) 20000,
        Real.exp (-(n : ℝ) / (gammaUpperCell2Scale : ℝ)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (gammaUpperCell2Scale : ℝ)) ≤
      (17674333 / 1000000 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat] using
    gamma_main_prefix_approx_upper (by norm_num only : 20000 ≤ 50000) gammaUpperCell2Exp
      (lt_of_lt_of_le zero_lt_one gamma_third_upper_scale_check.1)
      gamma_third_upper_scale_check.2.2.1 gamma_third_upper_scale_check.2.2.2
      (gammaUpperListCheck_sound gamma_third_upper_exp_check) gammaUpperCell2ChunksSum

/-- The infinite principal sum for the third cell is at most 17.684333.
Add the normalized tail bound to the finite certified upper sum; this is the
principal input for the third-cell Gamma gap. -/
theorem gamma_third_principal_upper :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (gammaUpperCell2Scale : ℝ)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (gammaUpperCell2Scale : ℝ)) ≤
      (17684333 / 1000000 : ℝ) := by
  have h :=
    gamma_principal_upper_small (by exact_mod_cast gamma_third_upper_scale_check.1)
      (by exact_mod_cast gamma_third_upper_scale_check.2.1) gamma_third_principal_finite
  norm_num only at h ⊢
  exact h

end PseudoPrime.PrimeTestBounds.MillerRabin
