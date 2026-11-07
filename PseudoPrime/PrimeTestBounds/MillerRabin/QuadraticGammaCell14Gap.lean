/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaCell14Principal
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaSecondCellBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaMainCellBlock9

/-! # Certified scalar Gamma gap for cell 14 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The rational right endpoint of Gamma cell 14. -/
def gammaCell14Right : ℚ :=
  43550736694879 / 1000000000000

/-- The checked Euler prefix through 563 exceeds the cell's rational cap.
Finite center-row verification supplies the lower estimate. -/
theorem gammaCell14_euler_lower :
    (40544 / 10000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 563, Analysis.gammaResolventMangoldtWeight n := by
  have hc :
    (40544 / 10000 : ℚ) ≤
      ((centerRowsBelow 563).map (fun r ↦ r.lo * Analysis.gammaFiniteEulerLower r.ratios)).sum := by
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using
    centerRowsBelow_euler_lower (by norm_num only : 563 ≤ 50000) (40544 / 10000) hc

/-- An integer-power comparison bounds the cell scale's negative `9/16`
power by the rational error cap. -/
theorem gammaCell14_power_upper : (gammaMainCell14Scale : ℝ) ^ (-9 / 16 : ℝ) ≤ 3648 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound
      (by norm_num only [gammaMainCell14Scale, Rat.cast_div, Rat.cast_ofNat]) (by norm_num only) 9
      16 (by decide)
  norm_num only [gammaMainCell14Scale, Rat.cast_div, Rat.cast_ofNat]

/-- Under RH, the principal, Euler and finite main-sum bounds give a strict
Gamma gap through the rational right endpoint of cell 14. -/
theorem gammaCell14_gap (hRH : RiemannHypothesis) {L : ℝ} (hL : L ≤ (gammaCell14Right : ℝ)) :
    (∑' k : ℕ,
              Real.exp (-(k : ℝ) / (gammaMainCell14Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
                Real.sqrt (gammaMainCell14Scale : ℝ)) +
            2 * (11783423 / 25000000 : ℝ) * L -
          477 / 100 +
        ((∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
          4 * ∑ k ∈ Finset.Ioc (0 : ℕ) 563, Analysis.gammaResolventMangoldtWeight k) +
        ((7 / 3 : ℝ) * L + 12) / Real.sqrt (gammaMainCell14Scale : ℝ) +
        (105 / 2 : ℝ) * (gammaMainCell14Scale : ℝ) ^ (-9 / 16 : ℝ) +
        3 / ((gammaMainCell14Scale : ℝ) * Real.sqrt (gammaMainCell14Scale : ℝ)) <
      4 *
        ∑ k ∈ Finset.Ioc (0 : ℕ) 563,
          Real.exp (-(k : ℝ) / (gammaMainCell14Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
            Real.sqrt (gammaMainCell14Scale : ℝ) := by
  apply
    gamma_gap_of_cell_caps (Finset.Ioc 0 563) (gammaMainCell14Scale : ℝ) L (gammaCell14Right : ℝ)
      (1897 / 100) (3648 / 100000) (gammaMainCell14Lower : ℝ) (18892955 / 1000000) (40544 / 10000)
      (by norm_num only [gammaMainCell14Scale, Rat.cast_div, Rat.cast_ofNat]) (by norm_num only)
      (by norm_num only [gammaMainCell14Scale, Rat.cast_div, Rat.cast_ofNat])
      (by norm_num only [gammaCell14Right, Rat.cast_div, Rat.cast_ofNat]) hL gammaCell14_power_upper
      gammaMainCell14_actual_lower
      (by
        simpa only [gammaUpperCell14Scale, gammaMainCell14Scale] using gammaCell14_principal_upper)
      gammaCell14_euler_lower (euler_mass_le_12372 hRH)
  norm_num only [gammaCell14Right, gammaMainCell14Scale, gammaMainCell14Lower, Rat.cast_div,
    Rat.cast_ofNat]

end PseudoPrime.PrimeTestBounds.MillerRabin
