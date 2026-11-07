/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaCell15Principal
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaSecondCellBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaMainCellBlock9

/-! # Certified scalar Gamma gap for cell 15 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The rational right endpoint of Gamma cell 15. -/
def gammaCell15Right : ℚ :=
  43627208635591 / 1000000000000

/-- The checked Euler prefix through 569 exceeds the cell's rational cap.
Finite center-row verification supplies the lower estimate. -/
theorem gammaCell15_euler_lower :
    (40595 / 10000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 569, Analysis.gammaResolventMangoldtWeight n := by
  have hc :
    (40595 / 10000 : ℚ) ≤
      ((centerRowsBelow 569).map (fun r ↦ r.lo * Analysis.gammaFiniteEulerLower r.ratios)).sum := by
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using
    centerRowsBelow_euler_lower (by norm_num only : 569 ≤ 50000) (40595 / 10000) hc

/-- An integer-power comparison bounds the cell scale's negative `9/16`
power by the rational error cap. -/
theorem gammaCell15_power_upper : (gammaMainCell15Scale : ℝ) ^ (-9 / 16 : ℝ) ≤ 3626 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound
      (by norm_num only [gammaMainCell15Scale, Rat.cast_div, Rat.cast_ofNat]) (by norm_num only) 9
      16 (by decide)
  norm_num only [gammaMainCell15Scale, Rat.cast_div, Rat.cast_ofNat]

/-- Under RH, the principal, Euler and finite main-sum bounds give a strict
Gamma gap through the rational right endpoint of cell 15. -/
theorem gammaCell15_gap (hRH : RiemannHypothesis) {L : ℝ} (hL : L ≤ (gammaCell15Right : ℝ)) :
    (∑' k : ℕ,
              Real.exp (-(k : ℝ) / (gammaMainCell15Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
                Real.sqrt (gammaMainCell15Scale : ℝ)) +
            2 * (11783423 / 25000000 : ℝ) * L -
          477 / 100 +
        ((∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
          4 * ∑ k ∈ Finset.Ioc (0 : ℕ) 569, Analysis.gammaResolventMangoldtWeight k) +
        ((7 / 3 : ℝ) * L + 12) / Real.sqrt (gammaMainCell15Scale : ℝ) +
        (105 / 2 : ℝ) * (gammaMainCell15Scale : ℝ) ^ (-9 / 16 : ℝ) +
        3 / ((gammaMainCell15Scale : ℝ) * Real.sqrt (gammaMainCell15Scale : ℝ)) <
      4 *
        ∑ k ∈ Finset.Ioc (0 : ℕ) 569,
          Real.exp (-(k : ℝ) / (gammaMainCell15Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
            Real.sqrt (gammaMainCell15Scale : ℝ) := by
  apply
    gamma_gap_of_cell_caps (Finset.Ioc 0 569) (gammaMainCell15Scale : ℝ) L (gammaCell15Right : ℝ)
      (1907 / 100) (3626 / 100000) (gammaMainCell15Lower : ℝ) (18991243 / 1000000) (40595 / 10000)
      (by norm_num only [gammaMainCell15Scale, Rat.cast_div, Rat.cast_ofNat]) (by norm_num only)
      (by norm_num only [gammaMainCell15Scale, Rat.cast_div, Rat.cast_ofNat])
      (by norm_num only [gammaCell15Right, Rat.cast_div, Rat.cast_ofNat]) hL gammaCell15_power_upper
      gammaMainCell15_actual_lower
      (by
        simpa only [gammaUpperCell15Scale, gammaMainCell15Scale] using gammaCell15_principal_upper)
      gammaCell15_euler_lower (euler_mass_le_12372 hRH)
  norm_num only [gammaCell15Right, gammaMainCell15Scale, gammaMainCell15Lower, Rat.cast_div,
    Rat.cast_ofNat]

end PseudoPrime.PrimeTestBounds.MillerRabin
