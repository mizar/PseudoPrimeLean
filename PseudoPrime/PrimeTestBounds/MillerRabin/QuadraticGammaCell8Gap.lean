/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaCell8Principal
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaSecondCellBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaMainCellBlock1

/-! # Certified scalar Gamma gap for cell 8 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The rational right endpoint of Gamma cell 8. -/
def gammaCell8Right : ℚ :=
  2609577711687 / 62500000000

/-- The checked Euler prefix through 521 exceeds the cell's rational cap.
Finite center-row verification supplies the lower estimate. -/
theorem gammaCell8_euler_lower :
    (40253 / 10000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 521, Analysis.gammaResolventMangoldtWeight n := by
  have hc :
    (40253 / 10000 : ℚ) ≤
      ((centerRowsBelow 521).map (fun r ↦ r.lo * Analysis.gammaFiniteEulerLower r.ratios)).sum := by
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using
    centerRowsBelow_euler_lower (by norm_num only : 521 ≤ 50000) (40253 / 10000) hc

/-- An integer-power comparison bounds the cell scale's negative `9/16`
power by the rational error cap. -/
theorem gammaCell8_power_upper : (gammaMainCell8Scale : ℝ) ^ (-9 / 16 : ℝ) ≤ 3793 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound
      (by norm_num only [gammaMainCell8Scale, Rat.cast_div, Rat.cast_ofNat]) (by norm_num only) 9 16
      (by decide)
  norm_num only [gammaMainCell8Scale, Rat.cast_div, Rat.cast_ofNat]

/-- Under RH, the principal, Euler and finite main-sum bounds give a strict
Gamma gap through the rational right endpoint of cell 8. -/
theorem gammaCell8_gap (hRH : RiemannHypothesis) {L : ℝ} (hL : L ≤ (gammaCell8Right : ℝ)) :
    (∑' k : ℕ,
              Real.exp (-(k : ℝ) / (gammaMainCell8Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
                Real.sqrt (gammaMainCell8Scale : ℝ)) +
            2 * (11783423 / 25000000 : ℝ) * L -
          477 / 100 +
        ((∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
          4 * ∑ k ∈ Finset.Ioc (0 : ℕ) 521, Analysis.gammaResolventMangoldtWeight k) +
        ((7 / 3 : ℝ) * L + 12) / Real.sqrt (gammaMainCell8Scale : ℝ) +
        (105 / 2 : ℝ) * (gammaMainCell8Scale : ℝ) ^ (-9 / 16 : ℝ) +
        3 / ((gammaMainCell8Scale : ℝ) * Real.sqrt (gammaMainCell8Scale : ℝ)) <
      4 *
        ∑ k ∈ Finset.Ioc (0 : ℕ) 521,
          Real.exp (-(k : ℝ) / (gammaMainCell8Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
            Real.sqrt (gammaMainCell8Scale : ℝ) := by
  apply
    gamma_gap_of_cell_caps (Finset.Ioc 0 521) (gammaMainCell8Scale : ℝ) L (gammaCell8Right : ℝ)
      (1833 / 100) (3793 / 100000) (gammaMainCell8Lower : ℝ) (18240500 / 1000000) (40253 / 10000)
      (by norm_num only [gammaMainCell8Scale, Rat.cast_div, Rat.cast_ofNat]) (by norm_num only)
      (by norm_num only [gammaMainCell8Scale, Rat.cast_div, Rat.cast_ofNat])
      (by norm_num only [gammaCell8Right, Rat.cast_div, Rat.cast_ofNat]) hL gammaCell8_power_upper
      gammaMainCell8_actual_lower
      (by simpa only [gammaUpperCell8Scale, gammaMainCell8Scale] using gammaCell8_principal_upper)
      gammaCell8_euler_lower (euler_mass_le_12372 hRH)
  norm_num only [gammaCell8Right, gammaMainCell8Scale, gammaMainCell8Lower, Rat.cast_div,
    Rat.cast_ofNat]

end PseudoPrime.PrimeTestBounds.MillerRabin
