/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaUpperCell1Chunks
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaPrincipalTail

/-! # Certified principal Gamma upper bound for the second middle cell -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- All rounded exponential endpoints cover the 20000 cutoff support.
The structural check verifies the Taylor bounds and exact list length. -/
theorem gamma_second_upper_exp_check :
    gammaUpperListCheck gammaUpperCell1Scale (centerRowsBelow 20000) gammaUpperCell1Exp = true := by
  decide +kernel

/-- The second-cell scale lies between one and 800 and the radius is a
positive lower bound for its square root. All checks use rational arithmetic. -/
theorem gamma_second_upper_scale_check :
    1 ≤ gammaUpperCell1Scale ∧
      gammaUpperCell1Scale ≤ 800 ∧
      0 < gammaUpperCell1Radius ∧ gammaUpperCell1Radius ^ 2 ≤ gammaUpperCell1Scale := by
  decide +kernel

/-- The finite normalized principal series through 20000 is at most 17.534153.
Use the checked Taylor endpoints, exact prime-power support and chunk sum. -/
theorem gamma_second_principal_finite :
    (∑ n ∈ Finset.Ioc (0 : ℕ) 20000,
        Real.exp (-(n : ℝ) / (gammaUpperCell1Scale : ℝ)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (gammaUpperCell1Scale : ℝ)) ≤
      (17534153 / 1000000 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat] using
    gamma_main_prefix_approx_upper (by norm_num only : 20000 ≤ 50000) gammaUpperCell1Exp
      (lt_of_lt_of_le zero_lt_one gamma_second_upper_scale_check.1)
      gamma_second_upper_scale_check.2.2.1 gamma_second_upper_scale_check.2.2.2
      (gammaUpperListCheck_sound gamma_second_upper_exp_check) gammaUpperCell1ChunksSum

/-- The infinite second-cell principal series is at most 17.544153.
Add the explicit 1/100 normalized tail to the finite certified upper bound. -/
theorem gamma_second_principal_upper :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (gammaUpperCell1Scale : ℝ)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (gammaUpperCell1Scale : ℝ)) ≤
      (17544153 / 1000000 : ℝ) := by
  have h :=
    gamma_principal_upper_small (by exact_mod_cast gamma_second_upper_scale_check.1)
      (by exact_mod_cast gamma_second_upper_scale_check.2.1) gamma_second_principal_finite
  norm_num only at h ⊢
  exact h

end PseudoPrime.PrimeTestBounds.MillerRabin
