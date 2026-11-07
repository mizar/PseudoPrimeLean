/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaCell3Principal
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaSecondCellBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaMainCellBlock1

/-! # Certified scalar Gamma gap for cell 3 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The rational right endpoint of Gamma cell 3. -/
def gammaCell3Right : ℚ :=
  5097997973061 / 125000000000

/-- The checked Euler prefix through 491 exceeds the cell's rational cap.
Finite center-row verification supplies the lower estimate. -/
theorem gammaCell3_euler_lower :
    (40020 / 10000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 491, Analysis.gammaResolventMangoldtWeight n := by
  have hc :
    (40020 / 10000 : ℚ) ≤
      ((centerRowsBelow 491).map (fun r ↦ r.lo * Analysis.gammaFiniteEulerLower r.ratios)).sum := by
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using
    centerRowsBelow_euler_lower (by norm_num only : 491 ≤ 50000) (40020 / 10000) hc

/-- An integer-power comparison bounds the cell scale's negative `9/16`
power by the rational error cap. -/
theorem gammaCell3_power_upper : (gammaMainCell3Scale : ℝ) ^ (-9 / 16 : ℝ) ≤ 3912 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound
      (by norm_num only [gammaMainCell3Scale, Rat.cast_div, Rat.cast_ofNat]) (by norm_num only) 9 16
      (by decide)
  norm_num only [gammaMainCell3Scale, Rat.cast_div, Rat.cast_ofNat]

/-- Under RH, the principal, Euler and finite main-sum bounds give a strict
Gamma gap through the rational right endpoint of cell 3. -/
theorem gammaCell3_gap (hRH : RiemannHypothesis) {L : ℝ} (hL : L ≤ (gammaCell3Right : ℝ)) :
    (∑' k : ℕ,
              Real.exp (-(k : ℝ) / (gammaMainCell3Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
                Real.sqrt (gammaMainCell3Scale : ℝ)) +
            2 * (11783423 / 25000000 : ℝ) * L -
          477 / 100 +
        ((∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
          4 * ∑ k ∈ Finset.Ioc (0 : ℕ) 491, Analysis.gammaResolventMangoldtWeight k) +
        ((7 / 3 : ℝ) * L + 12) / Real.sqrt (gammaMainCell3Scale : ℝ) +
        (105 / 2 : ℝ) * (gammaMainCell3Scale : ℝ) ^ (-9 / 16 : ℝ) +
        3 / ((gammaMainCell3Scale : ℝ) * Real.sqrt (gammaMainCell3Scale : ℝ)) <
      4 *
        ∑ k ∈ Finset.Ioc (0 : ℕ) 491,
          Real.exp (-(k : ℝ) / (gammaMainCell3Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
            Real.sqrt (gammaMainCell3Scale : ℝ) := by
  apply
    gamma_gap_of_cell_caps (Finset.Ioc 0 491) (gammaMainCell3Scale : ℝ) L (gammaCell3Right : ℝ)
      (1783 / 100) (3912 / 100000) (gammaMainCell3Lower : ℝ) (17743141 / 1000000) (40020 / 10000)
      (by norm_num only [gammaMainCell3Scale, Rat.cast_div, Rat.cast_ofNat]) (by norm_num only)
      (by norm_num only [gammaMainCell3Scale, Rat.cast_div, Rat.cast_ofNat])
      (by norm_num only [gammaCell3Right, Rat.cast_div, Rat.cast_ofNat]) hL gammaCell3_power_upper
      gammaMainCell3_actual_lower
      (by simpa only [gammaUpperCell3Scale, gammaMainCell3Scale] using gammaCell3_principal_upper)
      gammaCell3_euler_lower (euler_mass_le_12372 hRH)
  norm_num only [gammaCell3Right, gammaMainCell3Scale, gammaMainCell3Lower, Rat.cast_div,
    Rat.cast_ofNat]

end PseudoPrime.PrimeTestBounds.MillerRabin
