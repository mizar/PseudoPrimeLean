/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaCell4Principal
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaSecondCellBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaMainCellBlock1

/-! # Certified scalar Gamma gap for cell 4 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The rational right endpoint of Gamma cell 4. -/
def gammaCell4Right : ℚ :=
  5118390046359 / 125000000000

/-- The checked Euler prefix through 499 exceeds the cell's rational cap.
Finite center-row verification supplies the lower estimate. -/
theorem gammaCell4_euler_lower :
    (40078 / 10000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 499, Analysis.gammaResolventMangoldtWeight n := by
  have hc :
    (40078 / 10000 : ℚ) ≤
      ((centerRowsBelow 499).map (fun r ↦ r.lo * Analysis.gammaFiniteEulerLower r.ratios)).sum := by
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using
    centerRowsBelow_euler_lower (by norm_num only : 499 ≤ 50000) (40078 / 10000) hc

/-- An integer-power comparison bounds the cell scale's negative `9/16`
power by the rational error cap. -/
theorem gammaCell4_power_upper : (gammaMainCell4Scale : ℝ) ^ (-9 / 16 : ℝ) ≤ 3878 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound
      (by norm_num only [gammaMainCell4Scale, Rat.cast_div, Rat.cast_ofNat]) (by norm_num only) 9 16
      (by decide)
  norm_num only [gammaMainCell4Scale, Rat.cast_div, Rat.cast_ofNat]

/-- Under RH, the principal, Euler and finite main-sum bounds give a strict
Gamma gap through the rational right endpoint of cell 4. -/
theorem gammaCell4_gap (hRH : RiemannHypothesis) {L : ℝ} (hL : L ≤ (gammaCell4Right : ℝ)) :
    (∑' k : ℕ,
              Real.exp (-(k : ℝ) / (gammaMainCell4Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
                Real.sqrt (gammaMainCell4Scale : ℝ)) +
            2 * (11783423 / 25000000 : ℝ) * L -
          477 / 100 +
        ((∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
          4 * ∑ k ∈ Finset.Ioc (0 : ℕ) 499, Analysis.gammaResolventMangoldtWeight k) +
        ((7 / 3 : ℝ) * L + 12) / Real.sqrt (gammaMainCell4Scale : ℝ) +
        (105 / 2 : ℝ) * (gammaMainCell4Scale : ℝ) ^ (-9 / 16 : ℝ) +
        3 / ((gammaMainCell4Scale : ℝ) * Real.sqrt (gammaMainCell4Scale : ℝ)) <
      4 *
        ∑ k ∈ Finset.Ioc (0 : ℕ) 499,
          Real.exp (-(k : ℝ) / (gammaMainCell4Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
            Real.sqrt (gammaMainCell4Scale : ℝ) := by
  apply
    gamma_gap_of_cell_caps (Finset.Ioc 0 499) (gammaMainCell4Scale : ℝ) L (gammaCell4Right : ℝ)
      (1797 / 100) (3878 / 100000) (gammaMainCell4Lower : ℝ) (17881529 / 1000000) (40078 / 10000)
      (by norm_num only [gammaMainCell4Scale, Rat.cast_div, Rat.cast_ofNat]) (by norm_num only)
      (by norm_num only [gammaMainCell4Scale, Rat.cast_div, Rat.cast_ofNat])
      (by norm_num only [gammaCell4Right, Rat.cast_div, Rat.cast_ofNat]) hL gammaCell4_power_upper
      gammaMainCell4_actual_lower
      (by simpa only [gammaUpperCell4Scale, gammaMainCell4Scale] using gammaCell4_principal_upper)
      gammaCell4_euler_lower (euler_mass_le_12372 hRH)
  norm_num only [gammaCell4Right, gammaMainCell4Scale, gammaMainCell4Lower, Rat.cast_div,
    Rat.cast_ofNat]

end PseudoPrime.PrimeTestBounds.MillerRabin
