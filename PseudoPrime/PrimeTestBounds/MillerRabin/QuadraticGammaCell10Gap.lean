/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaCell10Principal
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaSecondCellBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaMainCellBlock9

/-! # Certified scalar Gamma gap for cell 10 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The rational right endpoint of Gamma cell 10. -/
def gammaCell10Right : ℚ :=
  42465672411177 / 1000000000000

/-- The checked Euler prefix through 529 exceeds the cell's rational cap.
Finite center-row verification supplies the lower estimate. -/
theorem gammaCell10_euler_lower :
    (40335 / 10000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 529, Analysis.gammaResolventMangoldtWeight n := by
  have hc :
    (40335 / 10000 : ℚ) ≤
      ((centerRowsBelow 529).map (fun r ↦ r.lo * Analysis.gammaFiniteEulerLower r.ratios)).sum := by
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using
    centerRowsBelow_euler_lower (by norm_num only : 529 ≤ 50000) (40335 / 10000) hc

/-- An integer-power comparison bounds the cell scale's negative `9/16`
power by the rational error cap. -/
theorem gammaCell10_power_upper : (gammaMainCell10Scale : ℝ) ^ (-9 / 16 : ℝ) ≤ 3768 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound
      (by norm_num only [gammaMainCell10Scale, Rat.cast_div, Rat.cast_ofNat]) (by norm_num only) 9
      16 (by decide)
  norm_num only [gammaMainCell10Scale, Rat.cast_div, Rat.cast_ofNat]

/-- Under RH, the principal, Euler and finite main-sum bounds give a strict
Gamma gap through the rational right endpoint of cell 10. -/
theorem gammaCell10_gap (hRH : RiemannHypothesis) {L : ℝ} (hL : L ≤ (gammaCell10Right : ℝ)) :
    (∑' k : ℕ,
              Real.exp (-(k : ℝ) / (gammaMainCell10Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
                Real.sqrt (gammaMainCell10Scale : ℝ)) +
            2 * (11783423 / 25000000 : ℝ) * L -
          477 / 100 +
        ((∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
          4 * ∑ k ∈ Finset.Ioc (0 : ℕ) 529, Analysis.gammaResolventMangoldtWeight k) +
        ((7 / 3 : ℝ) * L + 12) / Real.sqrt (gammaMainCell10Scale : ℝ) +
        (105 / 2 : ℝ) * (gammaMainCell10Scale : ℝ) ^ (-9 / 16 : ℝ) +
        3 / ((gammaMainCell10Scale : ℝ) * Real.sqrt (gammaMainCell10Scale : ℝ)) <
      4 *
        ∑ k ∈ Finset.Ioc (0 : ℕ) 529,
          Real.exp (-(k : ℝ) / (gammaMainCell10Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
            Real.sqrt (gammaMainCell10Scale : ℝ) := by
  apply
    gamma_gap_of_cell_caps (Finset.Ioc 0 529) (gammaMainCell10Scale : ℝ) L (gammaCell10Right : ℝ)
      (1844 / 100) (3768 / 100000) (gammaMainCell10Lower : ℝ) (18351450 / 1000000) (40335 / 10000)
      (by norm_num only [gammaMainCell10Scale, Rat.cast_div, Rat.cast_ofNat]) (by norm_num only)
      (by norm_num only [gammaMainCell10Scale, Rat.cast_div, Rat.cast_ofNat])
      (by norm_num only [gammaCell10Right, Rat.cast_div, Rat.cast_ofNat]) hL gammaCell10_power_upper
      gammaMainCell10_actual_lower
      (by
        simpa only [gammaUpperCell10Scale, gammaMainCell10Scale] using gammaCell10_principal_upper)
      gammaCell10_euler_lower (euler_mass_le_12372 hRH)
  norm_num only [gammaCell10Right, gammaMainCell10Scale, gammaMainCell10Lower, Rat.cast_div,
    Rat.cast_ofNat]

end PseudoPrime.PrimeTestBounds.MillerRabin
