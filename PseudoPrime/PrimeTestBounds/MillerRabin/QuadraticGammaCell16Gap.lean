/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaCell16Principal
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaSecondCellBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaMainCellBlock9

/-! # Certified scalar Gamma gap for cell 16 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The rational right endpoint of Gamma cell 16. -/
def gammaCell16Right : ℚ :=
  43855824394639 / 1000000000000

/-- The checked Euler prefix through 571 exceeds the cell's rational cap.
Finite center-row verification supplies the lower estimate. -/
theorem gammaCell16_euler_lower :
    (40646 / 10000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 571, Analysis.gammaResolventMangoldtWeight n := by
  have hc :
    (40646 / 10000 : ℚ) ≤
      ((centerRowsBelow 571).map (fun r ↦ r.lo * Analysis.gammaFiniteEulerLower r.ratios)).sum := by
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using
    centerRowsBelow_euler_lower (by norm_num only : 571 ≤ 50000) (40646 / 10000) hc

/-- An integer-power comparison bounds the cell scale's negative `9/16`
power by the rational error cap. -/
theorem gammaCell16_power_upper : (gammaMainCell16Scale : ℝ) ^ (-9 / 16 : ℝ) ≤ 3621 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound
      (by norm_num only [gammaMainCell16Scale, Rat.cast_div, Rat.cast_ofNat]) (by norm_num only) 9
      16 (by decide)
  norm_num only [gammaMainCell16Scale, Rat.cast_div, Rat.cast_ofNat]

/-- Under RH, the principal, Euler and finite main-sum bounds give a strict
Gamma gap through the rational right endpoint of cell 16. -/
theorem gammaCell16_gap (hRH : RiemannHypothesis) {L : ℝ} (hL : L ≤ (gammaCell16Right : ℝ)) :
    (∑' k : ℕ,
              Real.exp (-(k : ℝ) / (gammaMainCell16Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
                Real.sqrt (gammaMainCell16Scale : ℝ)) +
            2 * (11783423 / 25000000 : ℝ) * L -
          477 / 100 +
        ((∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
          4 * ∑ k ∈ Finset.Ioc (0 : ℕ) 571, Analysis.gammaResolventMangoldtWeight k) +
        ((7 / 3 : ℝ) * L + 12) / Real.sqrt (gammaMainCell16Scale : ℝ) +
        (105 / 2 : ℝ) * (gammaMainCell16Scale : ℝ) ^ (-9 / 16 : ℝ) +
        3 / ((gammaMainCell16Scale : ℝ) * Real.sqrt (gammaMainCell16Scale : ℝ)) <
      4 *
        ∑ k ∈ Finset.Ioc (0 : ℕ) 571,
          Real.exp (-(k : ℝ) / (gammaMainCell16Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
            Real.sqrt (gammaMainCell16Scale : ℝ) := by
  apply
    gamma_gap_of_cell_caps (Finset.Ioc 0 571) (gammaMainCell16Scale : ℝ) L (gammaCell16Right : ℝ)
      (1910 / 100) (3621 / 100000) (gammaMainCell16Lower : ℝ) (19015741 / 1000000) (40646 / 10000)
      (by norm_num only [gammaMainCell16Scale, Rat.cast_div, Rat.cast_ofNat]) (by norm_num only)
      (by norm_num only [gammaMainCell16Scale, Rat.cast_div, Rat.cast_ofNat])
      (by norm_num only [gammaCell16Right, Rat.cast_div, Rat.cast_ofNat]) hL gammaCell16_power_upper
      gammaMainCell16_actual_lower
      (by
        simpa only [gammaUpperCell16Scale, gammaMainCell16Scale] using gammaCell16_principal_upper)
      gammaCell16_euler_lower (euler_mass_le_12372 hRH)
  norm_num only [gammaCell16Right, gammaMainCell16Scale, gammaMainCell16Lower, Rat.cast_div,
    Rat.cast_ofNat]

end PseudoPrime.PrimeTestBounds.MillerRabin
