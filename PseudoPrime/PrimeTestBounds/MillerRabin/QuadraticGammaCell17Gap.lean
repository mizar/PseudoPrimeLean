/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaCell17Principal
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaSecondCellBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaMainCellBlock9

/-! # Certified scalar Gamma gap for cell 17 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The rational right endpoint of Gamma cell 17. -/
def gammaCell17Right : ℚ :=
  4423422506009 / 100000000000

/-- The checked Euler prefix through 577 exceeds the cell's rational cap.
Finite center-row verification supplies the lower estimate. -/
theorem gammaCell17_euler_lower :
    (40696 / 10000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 577, Analysis.gammaResolventMangoldtWeight n := by
  have hc :
    (40696 / 10000 : ℚ) ≤
      ((centerRowsBelow 577).map (fun r ↦ r.lo * Analysis.gammaFiniteEulerLower r.ratios)).sum := by
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using
    centerRowsBelow_euler_lower (by norm_num only : 577 ≤ 50000) (40696 / 10000) hc

/-- An integer-power comparison bounds the cell scale's negative `9/16`
power by the rational error cap. -/
theorem gammaCell17_power_upper : (gammaMainCell17Scale : ℝ) ^ (-9 / 16 : ℝ) ≤ 3603 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound
      (by norm_num only [gammaMainCell17Scale, Rat.cast_div, Rat.cast_ofNat]) (by norm_num only) 9
      16 (by decide)
  norm_num only [gammaMainCell17Scale, Rat.cast_div, Rat.cast_ofNat]

/-- Under RH, the principal, Euler and finite main-sum bounds give a strict
Gamma gap through the rational right endpoint of cell 17. -/
theorem gammaCell17_gap (hRH : RiemannHypothesis) {L : ℝ} (hL : L ≤ (gammaCell17Right : ℝ)) :
    (∑' k : ℕ,
              Real.exp (-(k : ℝ) / (gammaMainCell17Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
                Real.sqrt (gammaMainCell17Scale : ℝ)) +
            2 * (11783423 / 25000000 : ℝ) * L -
          477 / 100 +
        ((∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
          4 * ∑ k ∈ Finset.Ioc (0 : ℕ) 577, Analysis.gammaResolventMangoldtWeight k) +
        ((7 / 3 : ℝ) * L + 12) / Real.sqrt (gammaMainCell17Scale : ℝ) +
        (105 / 2 : ℝ) * (gammaMainCell17Scale : ℝ) ^ (-9 / 16 : ℝ) +
        3 / ((gammaMainCell17Scale : ℝ) * Real.sqrt (gammaMainCell17Scale : ℝ)) <
      4 *
        ∑ k ∈ Finset.Ioc (0 : ℕ) 577,
          Real.exp (-(k : ℝ) / (gammaMainCell17Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
            Real.sqrt (gammaMainCell17Scale : ℝ) := by
  apply
    gamma_gap_of_cell_caps (Finset.Ioc 0 577) (gammaMainCell17Scale : ℝ) L (gammaCell17Right : ℝ)
      (1918 / 100) (3603 / 100000) (gammaMainCell17Lower : ℝ) (19101321 / 1000000) (40696 / 10000)
      (by norm_num only [gammaMainCell17Scale, Rat.cast_div, Rat.cast_ofNat]) (by norm_num only)
      (by norm_num only [gammaMainCell17Scale, Rat.cast_div, Rat.cast_ofNat])
      (by norm_num only [gammaCell17Right, Rat.cast_div, Rat.cast_ofNat]) hL gammaCell17_power_upper
      gammaMainCell17_actual_lower
      (by
        simpa only [gammaUpperCell17Scale, gammaMainCell17Scale] using gammaCell17_principal_upper)
      gammaCell17_euler_lower (euler_mass_le_12372 hRH)
  norm_num only [gammaCell17Right, gammaMainCell17Scale, gammaMainCell17Lower, Rat.cast_div,
    Rat.cast_ofNat]

end PseudoPrime.PrimeTestBounds.MillerRabin
