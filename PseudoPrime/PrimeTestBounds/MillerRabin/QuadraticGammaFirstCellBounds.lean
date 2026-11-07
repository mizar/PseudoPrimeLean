/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaMainCellBlock0
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaScalarTransfer
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerCenterBound

/-! # Fixed scalar inputs for the first middle Gamma cell -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The first finite-cell right endpoint, retained as a rational number.
It is an upper enclosure for the next prime-power switching point.
The cell comparison below is valid for every real parameter below it. -/
def gammaFirstRight : ℚ :=
  3995831160931 / 100000000000

/-- Exact row aggregation gives Euler prefix lower cap 3.984 through 477.
The checked root and logarithm intervals are inherited from the center rows.
This cap leaves a positive scalar margin with the coarse first-cell errors. -/
theorem gamma_first_euler_check :
    (498 / 125 : ℚ) ≤
      ((centerRowsBelow 477).map (fun r ↦ r.lo * Analysis.gammaFiniteEulerLower r.ratios)).sum := by
  decide +kernel

/-- The actual Euler prefix through 477 is at least 3.984.
Transfer exact support and the rational row aggregation to the real sum. -/
theorem gamma_first_euler_lower :
    (498 / 125 : ℝ) ≤ ∑ n ∈ Finset.Ioc (0 : ℕ) 477, Analysis.gammaResolventMangoldtWeight n := by
  simpa only [Rat.cast_div, Rat.cast_ofNat] using
    centerRowsBelow_euler_lower (by norm_num only : 477 ≤ 50000) (498 / 125) gamma_first_euler_check

/-- The first fixed scale satisfies a rational upper bound 1/25 for its
negative 9/16 power. Integer-power arithmetic certifies the endpoint and
the existing real-power transfer proves the actual analytic inequality. -/
theorem gamma_first_power_upper : (gammaMainCell0Scale : ℝ) ^ (-9 / 16 : ℝ) ≤ 1 / 25 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound
      (by norm_num only [gammaMainCell0Scale, Rat.cast_div, Rat.cast_ofNat]) (by norm_num only) 9 16
      (by decide)
  norm_num only [gammaMainCell0Scale, Rat.cast_div, Rat.cast_ofNat]

/-- Coarse fixed endpoints still give a strict positive first-cell margin.
All inputs are rational, including the square-root lower cap 17.61,
the principal upper cap 17.522 and the retained finite-main lower cap. -/
theorem gamma_first_scalar_check :
    (8761 / 500 : ℚ) + 2 * (11783423 / 25000000) * gammaFirstRight - 477 / 100 +
        (3093 / 250 - 4 * (498 / 125)) +
        ((7 / 3) * gammaFirstRight + 12) / (1761 / 100) +
        (105 / 2) * (1 / 25) +
        3 / (gammaMainCell0Scale * (1761 / 100)) <
      4 * gammaMainCell0Lower := by
  decide +kernel

/-- The certified first-cell scalar inputs imply the actual Gamma gap once
the principal series is bounded by 17.522. The logarithmic parameter may vary
through the entire cell up to its rational right endpoint. The remaining
principal bound is discharged separately by the finite sum and tail. -/
theorem gamma_first_gap_of_principal (hRH : RiemannHypothesis) {L : ℝ}
    (hL : L ≤ (gammaFirstRight : ℝ))
    (hU :
      (∑' k : ℕ,
          Real.exp (-(k : ℝ) / (gammaMainCell0Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
            Real.sqrt (gammaMainCell0Scale : ℝ)) ≤
        8761 / 500) :
    (∑' k : ℕ,
              Real.exp (-(k : ℝ) / (gammaMainCell0Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
                Real.sqrt (gammaMainCell0Scale : ℝ)) +
            2 * (11783423 / 25000000 : ℝ) * L -
          477 / 100 +
        ((∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
          4 * ∑ k ∈ Finset.Ioc (0 : ℕ) 477, Analysis.gammaResolventMangoldtWeight k) +
        ((7 / 3 : ℝ) * L + 12) / Real.sqrt (gammaMainCell0Scale : ℝ) +
        (105 / 2 : ℝ) * (gammaMainCell0Scale : ℝ) ^ (-9 / 16 : ℝ) +
        3 / ((gammaMainCell0Scale : ℝ) * Real.sqrt (gammaMainCell0Scale : ℝ)) <
      4 *
        ∑ k ∈ Finset.Ioc (0 : ℕ) 477,
          Real.exp (-(k : ℝ) / (gammaMainCell0Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
            Real.sqrt (gammaMainCell0Scale : ℝ) := by
  apply
    gamma_gap_of_cell_caps (Finset.Ioc 0 477) (gammaMainCell0Scale : ℝ) L (gammaFirstRight : ℝ)
      (1761 / 100) (1 / 25) (gammaMainCell0Lower : ℝ) (8761 / 500) (498 / 125)
      (by norm_num only [gammaMainCell0Scale, Rat.cast_div, Rat.cast_ofNat]) (by norm_num only)
      (by norm_num only [gammaMainCell0Scale, Rat.cast_div, Rat.cast_ofNat])
      (by norm_num only [gammaFirstRight, Rat.cast_div, Rat.cast_ofNat]) hL gamma_first_power_upper
      gammaMainCell0_actual_lower hU gamma_first_euler_lower (euler_mass_le_12372 hRH)
  norm_num only [gammaFirstRight, gammaMainCell0Scale, gammaMainCell0Lower, Rat.cast_div,
    Rat.cast_ofNat]

end PseudoPrime.PrimeTestBounds.MillerRabin
