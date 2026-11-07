/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaThirdPrincipal
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaSecondCellBounds

/-! # Certified scalar Gamma gap for the third middle cell -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The right endpoint of the third finite Gamma cell. -/
def gammaThirdRight : ℚ :=
  40455737129197 / 1000000000000

/-- The Euler prefix through 487 exceeds the rational cap used for the third
cell. Checked center rows transfer the rational sum to the real prefix. -/
theorem gamma_third_euler_lower :
    (999 / 250 : ℝ) ≤ ∑ n ∈ Finset.Ioc (0 : ℕ) 487, Analysis.gammaResolventMangoldtWeight n := by
  have hc :
    (999 / 250 : ℚ) ≤
      ((centerRowsBelow 487).map (fun r ↦ r.lo * Analysis.gammaFiniteEulerLower r.ratios)).sum := by
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using
    centerRowsBelow_euler_lower (by norm_num only : 487 ≤ 50000) (999 / 250) hc

/-- The third fixed scale has negative `9/16` power at most `395/10000`.
An integer-power comparison certifies this analytic error cap. -/
theorem gamma_third_power_upper : (gammaMainCell2Scale : ℝ) ^ (-9 / 16 : ℝ) ≤ 395 / 10000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound
      (by norm_num only [gammaMainCell2Scale, Rat.cast_div, Rat.cast_ofNat]) (by norm_num only) 9 16
      (by decide)
  norm_num only [gammaMainCell2Scale, Rat.cast_div, Rat.cast_ofNat]

/-- Under RH, the certified third-cell inputs reverse the Gamma inequality
throughout the cell up to its right endpoint. The principal upper sum includes
the infinite tail, and the remaining inputs are finite certified bounds. -/
theorem gamma_third_gap (hRH : RiemannHypothesis) {L : ℝ} (hL : L ≤ (gammaThirdRight : ℝ)) :
    (∑' k : ℕ,
              Real.exp (-(k : ℝ) / (gammaMainCell2Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
                Real.sqrt (gammaMainCell2Scale : ℝ)) +
            2 * (11783423 / 25000000 : ℝ) * L -
          477 / 100 +
        ((∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
          4 * ∑ k ∈ Finset.Ioc (0 : ℕ) 487, Analysis.gammaResolventMangoldtWeight k) +
        ((7 / 3 : ℝ) * L + 12) / Real.sqrt (gammaMainCell2Scale : ℝ) +
        (105 / 2 : ℝ) * (gammaMainCell2Scale : ℝ) ^ (-9 / 16 : ℝ) +
        3 / ((gammaMainCell2Scale : ℝ) * Real.sqrt (gammaMainCell2Scale : ℝ)) <
      4 *
        ∑ k ∈ Finset.Ioc (0 : ℕ) 487,
          Real.exp (-(k : ℝ) / (gammaMainCell2Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
            Real.sqrt (gammaMainCell2Scale : ℝ) := by
  apply
    gamma_gap_of_cell_caps (Finset.Ioc 0 487) (gammaMainCell2Scale : ℝ) L (gammaThirdRight : ℝ)
      (1777 / 100) (395 / 10000) (gammaMainCell2Lower : ℝ) (17684333 / 1000000) (999 / 250)
      (by norm_num only [gammaMainCell2Scale, Rat.cast_div, Rat.cast_ofNat]) (by norm_num only)
      (by norm_num only [gammaMainCell2Scale, Rat.cast_div, Rat.cast_ofNat])
      (by norm_num only [gammaThirdRight, Rat.cast_div, Rat.cast_ofNat]) hL gamma_third_power_upper
      gammaMainCell2_actual_lower
      (by simpa only [gammaUpperCell2Scale, gammaMainCell2Scale] using gamma_third_principal_upper)
      gamma_third_euler_lower (euler_mass_le_12372 hRH)
  norm_num only [gammaThirdRight, gammaMainCell2Scale, gammaMainCell2Lower, Rat.cast_div,
    Rat.cast_ofNat]

end PseudoPrime.PrimeTestBounds.MillerRabin
