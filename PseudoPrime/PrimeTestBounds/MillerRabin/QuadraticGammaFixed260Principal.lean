/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaPrincipalRH
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaMainCellBlock249
public import PseudoPrime.Analysis.LogTaylorBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaSecondCellBounds

/-! # Principal cap at the shared scale of Gamma cell 260 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under the Riemann hypothesis the principal sum at the shared scale is
at most 36.87. Rational square-root and logarithm bounds certify the
signed-variation estimate for use in the subsequent finite-cell comparisons. -/
theorem gammaFixed260_principal_upper (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (gammaMainCell260Scale : ℝ)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (gammaMainCell260Scale : ℝ)) ≤
      3687 / 100 := by
  have hc : Analysis.rationalLogIntervalCheck gammaMainCell260Scale 11 20 0 (899 / 125) = true := by
    decide +kernel
  have hl := (Analysis.rationalLogIntervalCheck_sound hc).2
  have hlog : Real.log (gammaMainCell260Scale : ℝ) ≤ (899 / 125 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using hl
  have hlo : (3645 / 100 : ℝ) ≤ Real.sqrt (gammaMainCell260Scale : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    norm_num only [gammaMainCell260Scale, Rat.cast_div, Rat.cast_ofNat]
  have hhi : Real.sqrt (gammaMainCell260Scale : ℝ) ≤ (3646 / 100 : ℝ) := by
    apply (Real.sqrt_le_iff).2
    constructor <;> norm_num only [gammaMainCell260Scale, Rat.cast_div, Rat.cast_ofNat]
  apply
    gamma_principal_upper_rh_cap hRH (R := 3645 / 100) (T := 3646 / 100) (Z := 899 / 125)
      (by norm_num only [gammaMainCell260Scale, Rat.cast_div, Rat.cast_ofNat]) (by norm_num only)
      hlo hhi hlog (by norm_num only)
  norm_num only

/-- The negative `9/16` power of the shared scale is at most `1751/100000`.
An exact integer-power comparison supplies the scalar error bound used in
Gamma-cell comparisons. -/
theorem gammaFixed260_power_upper :
    (gammaMainCell260Scale : ℝ) ^ (-9 / 16 : ℝ) ≤ 1751 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound
      (by norm_num only [gammaMainCell260Scale, Rat.cast_div, Rat.cast_ofNat]) (by norm_num only) 9
      16 (by decide)
  norm_num only [gammaMainCell260Scale, Rat.cast_div, Rat.cast_ofNat]

end PseudoPrime.PrimeTestBounds.MillerRabin
