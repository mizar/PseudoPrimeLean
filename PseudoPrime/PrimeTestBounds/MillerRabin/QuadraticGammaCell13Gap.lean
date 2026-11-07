/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaCell13Principal
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaSecondCellBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaMainCellBlock9

/-! # Certified scalar Gamma gap for cell 13 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The rational right endpoint of Gamma cell 13. -/
def gammaCell13Right : ℚ :=
  21660255461713 / 500000000000

/-- The checked Euler prefix through 557 exceeds the cell's rational cap.
Finite center-row verification supplies the lower estimate. -/
theorem gammaCell13_euler_lower :
    (40493 / 10000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 557, Analysis.gammaResolventMangoldtWeight n := by
  have hc :
    (40493 / 10000 : ℚ) ≤
      ((centerRowsBelow 557).map (fun r ↦ r.lo * Analysis.gammaFiniteEulerLower r.ratios)).sum := by
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using
    centerRowsBelow_euler_lower (by norm_num only : 557 ≤ 50000) (40493 / 10000) hc

/-- An integer-power comparison bounds the cell scale's negative `9/16`
power by the rational error cap. -/
theorem gammaCell13_power_upper : (gammaMainCell13Scale : ℝ) ^ (-9 / 16 : ℝ) ≤ 3668 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound
      (by norm_num only [gammaMainCell13Scale, Rat.cast_div, Rat.cast_ofNat]) (by norm_num only) 9
      16 (by decide)
  norm_num only [gammaMainCell13Scale, Rat.cast_div, Rat.cast_ofNat]

/-- Under RH, the principal, Euler and finite main-sum bounds give a strict
Gamma gap through the rational right endpoint of cell 13. -/
theorem gammaCell13_gap (hRH : RiemannHypothesis) {L : ℝ} (hL : L ≤ (gammaCell13Right : ℝ)) :
    (∑' k : ℕ,
              Real.exp (-(k : ℝ) / (gammaMainCell13Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
                Real.sqrt (gammaMainCell13Scale : ℝ)) +
            2 * (11783423 / 25000000 : ℝ) * L -
          477 / 100 +
        ((∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
          4 * ∑ k ∈ Finset.Ioc (0 : ℕ) 557, Analysis.gammaResolventMangoldtWeight k) +
        ((7 / 3 : ℝ) * L + 12) / Real.sqrt (gammaMainCell13Scale : ℝ) +
        (105 / 2 : ℝ) * (gammaMainCell13Scale : ℝ) ^ (-9 / 16 : ℝ) +
        3 / ((gammaMainCell13Scale : ℝ) * Real.sqrt (gammaMainCell13Scale : ℝ)) <
      4 *
        ∑ k ∈ Finset.Ioc (0 : ℕ) 557,
          Real.exp (-(k : ℝ) / (gammaMainCell13Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
            Real.sqrt (gammaMainCell13Scale : ℝ) := by
  apply
    gamma_gap_of_cell_caps (Finset.Ioc 0 557) (gammaMainCell13Scale : ℝ) L (gammaCell13Right : ℝ)
      (1888 / 100) (3668 / 100000) (gammaMainCell13Lower : ℝ) (18800300 / 1000000) (40493 / 10000)
      (by norm_num only [gammaMainCell13Scale, Rat.cast_div, Rat.cast_ofNat]) (by norm_num only)
      (by norm_num only [gammaMainCell13Scale, Rat.cast_div, Rat.cast_ofNat])
      (by norm_num only [gammaCell13Right, Rat.cast_div, Rat.cast_ofNat]) hL gammaCell13_power_upper
      gammaMainCell13_actual_lower
      (by
        simpa only [gammaUpperCell13Scale, gammaMainCell13Scale] using gammaCell13_principal_upper)
      gammaCell13_euler_lower (euler_mass_le_12372 hRH)
  norm_num only [gammaCell13Right, gammaMainCell13Scale, gammaMainCell13Lower, Rat.cast_div,
    Rat.cast_ofNat]

end PseudoPrime.PrimeTestBounds.MillerRabin
