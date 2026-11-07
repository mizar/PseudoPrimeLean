/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaCell9Principal
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaSecondCellBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaMainCellBlock9

/-! # Certified scalar Gamma gap for cell 9 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The rational right endpoint of Gamma cell 9. -/
def gammaCell9Right : ℚ :=
  41992062742063 / 1000000000000

/-- The checked Euler prefix through 523 exceeds the cell's rational cap.
Finite center-row verification supplies the lower estimate. -/
theorem gammaCell9_euler_lower :
    (40308 / 10000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 523, Analysis.gammaResolventMangoldtWeight n := by
  have hc :
    (40308 / 10000 : ℚ) ≤
      ((centerRowsBelow 523).map (fun r ↦ r.lo * Analysis.gammaFiniteEulerLower r.ratios)).sum := by
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using
    centerRowsBelow_euler_lower (by norm_num only : 523 ≤ 50000) (40308 / 10000) hc

/-- An integer-power comparison bounds the cell scale's negative `9/16`
power by the rational error cap. -/
theorem gammaCell9_power_upper : (gammaMainCell9Scale : ℝ) ^ (-9 / 16 : ℝ) ≤ 3787 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound
      (by norm_num only [gammaMainCell9Scale, Rat.cast_div, Rat.cast_ofNat]) (by norm_num only) 9 16
      (by decide)
  norm_num only [gammaMainCell9Scale, Rat.cast_div, Rat.cast_ofNat]

/-- Under RH, the principal, Euler and finite main-sum bounds give a strict
Gamma gap through the rational right endpoint of cell 9. -/
theorem gammaCell9_gap (hRH : RiemannHypothesis) {L : ℝ} (hL : L ≤ (gammaCell9Right : ℝ)) :
    (∑' k : ℕ,
              Real.exp (-(k : ℝ) / (gammaMainCell9Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
                Real.sqrt (gammaMainCell9Scale : ℝ)) +
            2 * (11783423 / 25000000 : ℝ) * L -
          477 / 100 +
        ((∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
          4 * ∑ k ∈ Finset.Ioc (0 : ℕ) 523, Analysis.gammaResolventMangoldtWeight k) +
        ((7 / 3 : ℝ) * L + 12) / Real.sqrt (gammaMainCell9Scale : ℝ) +
        (105 / 2 : ℝ) * (gammaMainCell9Scale : ℝ) ^ (-9 / 16 : ℝ) +
        3 / ((gammaMainCell9Scale : ℝ) * Real.sqrt (gammaMainCell9Scale : ℝ)) <
      4 *
        ∑ k ∈ Finset.Ioc (0 : ℕ) 523,
          Real.exp (-(k : ℝ) / (gammaMainCell9Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
            Real.sqrt (gammaMainCell9Scale : ℝ) := by
  apply
    gamma_gap_of_cell_caps (Finset.Ioc 0 523) (gammaMainCell9Scale : ℝ) L (gammaCell9Right : ℝ)
      (1835 / 100) (3787 / 100000) (gammaMainCell9Lower : ℝ) (18265710 / 1000000) (40308 / 10000)
      (by norm_num only [gammaMainCell9Scale, Rat.cast_div, Rat.cast_ofNat]) (by norm_num only)
      (by norm_num only [gammaMainCell9Scale, Rat.cast_div, Rat.cast_ofNat])
      (by norm_num only [gammaCell9Right, Rat.cast_div, Rat.cast_ofNat]) hL gammaCell9_power_upper
      gammaMainCell9_actual_lower
      (by simpa only [gammaUpperCell9Scale, gammaMainCell9Scale] using gammaCell9_principal_upper)
      gammaCell9_euler_lower (euler_mass_le_12372 hRH)
  norm_num only [gammaCell9Right, gammaMainCell9Scale, gammaMainCell9Lower, Rat.cast_div,
    Rat.cast_ofNat]

end PseudoPrime.PrimeTestBounds.MillerRabin
