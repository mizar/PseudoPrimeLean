/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaUpperCell0Chunks
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaPrincipalTail

/-! # Certified principal Gamma upper bound for the first middle cell -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- All rounded exponential endpoints cover the 20000 cutoff support.
The structural check verifies the Taylor bounds and exact list length. -/
theorem gamma_first_upper_exp_check :
    gammaUpperListCheck gammaUpperCell0Scale (centerRowsBelow 20000) gammaUpperCell0Exp = true := by
  decide +kernel

/-- The first-cell scale lies between one and 800 and the radius is a
positive lower bound for its square root. All checks use rational arithmetic. -/
theorem gamma_first_upper_scale_check :
    1 ≤ gammaUpperCell0Scale ∧
      gammaUpperCell0Scale ≤ 800 ∧
      0 < gammaUpperCell0Radius ∧ gammaUpperCell0Radius ^ 2 ≤ gammaUpperCell0Scale := by
  decide +kernel

/-- The finite normalized principal series through 20000 is at most 17.512.
Use the checked Taylor endpoints, exact prime-power support and chunk sum. -/
theorem gamma_first_principal_finite :
    (∑ n ∈ Finset.Ioc (0 : ℕ) 20000,
        Real.exp (-(n : ℝ) / (gammaUpperCell0Scale : ℝ)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (gammaUpperCell0Scale : ℝ)) ≤
      (17512 / 1000 : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat] using
    gamma_main_prefix_approx_upper (by norm_num only : 20000 ≤ 50000) gammaUpperCell0Exp
      (lt_of_lt_of_le zero_lt_one gamma_first_upper_scale_check.1)
      gamma_first_upper_scale_check.2.2.1 gamma_first_upper_scale_check.2.2.2
      (gammaUpperListCheck_sound gamma_first_upper_exp_check) upperChunksSum

/-- The infinite first-cell principal series is at most 17.522.
Add the explicit 1/100 normalized tail to the finite certified upper bound. -/
theorem gamma_first_principal_upper :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (gammaUpperCell0Scale : ℝ)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (gammaUpperCell0Scale : ℝ)) ≤
      (8761 / 500 : ℝ) := by
  have h :=
    gamma_principal_upper_small (by exact_mod_cast gamma_first_upper_scale_check.1)
      (by exact_mod_cast gamma_first_upper_scale_check.2.1) gamma_first_principal_finite
  norm_num only at h ⊢
  exact h

end PseudoPrime.PrimeTestBounds.MillerRabin
