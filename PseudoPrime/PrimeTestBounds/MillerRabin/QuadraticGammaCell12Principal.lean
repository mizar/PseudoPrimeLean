/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaUpperCell12Chunks
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaPrincipalTail

/-! # Principal Gamma upper bound for cell 12 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

set_option maxRecDepth 8192 in
/-- The upper exponential data cover every prime-power row through 20000.
The structural check verifies each Taylor endpoint and the support alignment. -/
theorem gammaCell12_upper_exp_check :
    gammaUpperListCheck gammaUpperCell12Scale (centerRowsBelow 20000) gammaUpperCell12Exp =
      true := by
  decide +kernel

/-- The cell scale and radius satisfy the hypotheses of the normalized
principal-tail estimate and the finite sum transfer. -/
theorem gammaCell12_upper_scale_check :
    1 ≤ gammaUpperCell12Scale ∧
      gammaUpperCell12Scale ≤ 800 ∧
      0 < gammaUpperCell12Radius ∧ gammaUpperCell12Radius ^ 2 ≤ gammaUpperCell12Scale := by
  decide +kernel

/-- The finite principal sum is at most its certified chunk total.
The upper endpoint checks and support alignment bound every term. -/
theorem gammaCell12_principal_finite :
    (∑ n ∈ Finset.Ioc (0 : ℕ) 20000,
        Real.exp (-(n : ℝ) / (gammaUpperCell12Scale : ℝ)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (gammaUpperCell12Scale : ℝ)) ≤
      (18628455 / 1000000 : ℝ) := by
  have h :=
    gamma_main_prefix_approx_upper (by norm_num only : 20000 ≤ 50000) gammaUpperCell12Exp
      (lt_of_lt_of_le zero_lt_one gammaCell12_upper_scale_check.1)
      gammaCell12_upper_scale_check.2.2.1 gammaCell12_upper_scale_check.2.2.2
      (gammaUpperListCheck_sound gammaCell12_upper_exp_check) gammaUpperCell12ChunksSum
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h ⊢
  exact h

/-- The infinite principal sum is bounded by the finite cap plus the explicit
normalized tail `1/100`. This supplies a rigorous input to the cell gap. -/
theorem gammaCell12_principal_upper :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (gammaUpperCell12Scale : ℝ)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (gammaUpperCell12Scale : ℝ)) ≤
      (18638455 / 1000000 : ℝ) := by
  have h :=
    gamma_principal_upper_small (by exact_mod_cast gammaCell12_upper_scale_check.1)
      (by exact_mod_cast gammaCell12_upper_scale_check.2.1) gammaCell12_principal_finite
  norm_num only at h ⊢
  exact h

end PseudoPrime.PrimeTestBounds.MillerRabin
