/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaCell12Principal
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaSecondCellBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaMainCellBlock9

/-! # Certified scalar Gamma gap for cell 12 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The rational right endpoint of Gamma cell 12. -/
def gammaCell12Right : ℚ :=
  21544527534079 / 500000000000

/-- The checked Euler prefix through 547 exceeds the cell's rational cap.
Finite center-row verification supplies the lower estimate. -/
theorem gammaCell12_euler_lower :
    (40441 / 10000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 547, Analysis.gammaResolventMangoldtWeight n := by
  have hc :
    (40441 / 10000 : ℚ) ≤
      ((centerRowsBelow 547).map (fun r ↦ r.lo * Analysis.gammaFiniteEulerLower r.ratios)).sum := by
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using
    centerRowsBelow_euler_lower (by norm_num only : 547 ≤ 50000) (40441 / 10000) hc

/-- An integer-power comparison bounds the cell scale's negative `9/16`
power by the rational error cap. -/
theorem gammaCell12_power_upper : (gammaMainCell12Scale : ℝ) ^ (-9 / 16 : ℝ) ≤ 3703 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound
      (by norm_num only [gammaMainCell12Scale, Rat.cast_div, Rat.cast_ofNat]) (by norm_num only) 9
      16 (by decide)
  norm_num only [gammaMainCell12Scale, Rat.cast_div, Rat.cast_ofNat]

/-- Under RH, the principal, Euler and finite main-sum bounds give a strict
Gamma gap through the rational right endpoint of cell 12. -/
theorem gammaCell12_gap (hRH : RiemannHypothesis) {L : ℝ} (hL : L ≤ (gammaCell12Right : ℝ)) :
    (∑' k : ℕ,
              Real.exp (-(k : ℝ) / (gammaMainCell12Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
                Real.sqrt (gammaMainCell12Scale : ℝ)) +
            2 * (11783423 / 25000000 : ℝ) * L -
          477 / 100 +
        ((∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
          4 * ∑ k ∈ Finset.Ioc (0 : ℕ) 547, Analysis.gammaResolventMangoldtWeight k) +
        ((7 / 3 : ℝ) * L + 12) / Real.sqrt (gammaMainCell12Scale : ℝ) +
        (105 / 2 : ℝ) * (gammaMainCell12Scale : ℝ) ^ (-9 / 16 : ℝ) +
        3 / ((gammaMainCell12Scale : ℝ) * Real.sqrt (gammaMainCell12Scale : ℝ)) <
      4 *
        ∑ k ∈ Finset.Ioc (0 : ℕ) 547,
          Real.exp (-(k : ℝ) / (gammaMainCell12Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
            Real.sqrt (gammaMainCell12Scale : ℝ) := by
  apply
    gamma_gap_of_cell_caps (Finset.Ioc 0 547) (gammaMainCell12Scale : ℝ) L (gammaCell12Right : ℝ)
      (1872 / 100) (3703 / 100000) (gammaMainCell12Lower : ℝ) (18638455 / 1000000) (40441 / 10000)
      (by norm_num only [gammaMainCell12Scale, Rat.cast_div, Rat.cast_ofNat]) (by norm_num only)
      (by norm_num only [gammaMainCell12Scale, Rat.cast_div, Rat.cast_ofNat])
      (by norm_num only [gammaCell12Right, Rat.cast_div, Rat.cast_ofNat]) hL gammaCell12_power_upper
      gammaMainCell12_actual_lower
      (by
        simpa only [gammaUpperCell12Scale, gammaMainCell12Scale] using gammaCell12_principal_upper)
      gammaCell12_euler_lower (euler_mass_le_12372 hRH)
  norm_num only [gammaCell12Right, gammaMainCell12Scale, gammaMainCell12Lower, Rat.cast_div,
    Rat.cast_ofNat]

end PseudoPrime.PrimeTestBounds.MillerRabin
