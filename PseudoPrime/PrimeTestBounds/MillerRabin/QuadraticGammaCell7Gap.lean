/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaCell7Principal
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaSecondCellBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaMainCellBlock1

/-! # Certified scalar Gamma gap for cell 7 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The rational right endpoint of Gamma cell 7. -/
def gammaCell7Right : ℚ :=
  20836666400043 / 500000000000

/-- The checked Euler prefix through 512 exceeds the cell's rational cap.
Finite center-row verification supplies the lower estimate. -/
theorem gammaCell7_euler_lower :
    (40197 / 10000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 512, Analysis.gammaResolventMangoldtWeight n := by
  have hc :
    (40197 / 10000 : ℚ) ≤
      ((centerRowsBelow 512).map (fun r ↦ r.lo * Analysis.gammaFiniteEulerLower r.ratios)).sum := by
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using
    centerRowsBelow_euler_lower (by norm_num only : 512 ≤ 50000) (40197 / 10000) hc

/-- An integer-power comparison bounds the cell scale's negative `9/16`
power by the rational error cap. -/
theorem gammaCell7_power_upper : (gammaMainCell7Scale : ℝ) ^ (-9 / 16 : ℝ) ≤ 3830 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound
      (by norm_num only [gammaMainCell7Scale, Rat.cast_div, Rat.cast_ofNat]) (by norm_num only) 9 16
      (by decide)
  norm_num only [gammaMainCell7Scale, Rat.cast_div, Rat.cast_ofNat]

/-- Under RH, the principal, Euler and finite main-sum bounds give a strict
Gamma gap through the rational right endpoint of cell 7. -/
theorem gammaCell7_gap (hRH : RiemannHypothesis) {L : ℝ} (hL : L ≤ (gammaCell7Right : ℝ)) :
    (∑' k : ℕ,
              Real.exp (-(k : ℝ) / (gammaMainCell7Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
                Real.sqrt (gammaMainCell7Scale : ℝ)) +
            2 * (11783423 / 25000000 : ℝ) * L -
          477 / 100 +
        ((∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
          4 * ∑ k ∈ Finset.Ioc (0 : ℕ) 512, Analysis.gammaResolventMangoldtWeight k) +
        ((7 / 3 : ℝ) * L + 12) / Real.sqrt (gammaMainCell7Scale : ℝ) +
        (105 / 2 : ℝ) * (gammaMainCell7Scale : ℝ) ^ (-9 / 16 : ℝ) +
        3 / ((gammaMainCell7Scale : ℝ) * Real.sqrt (gammaMainCell7Scale : ℝ)) <
      4 *
        ∑ k ∈ Finset.Ioc (0 : ℕ) 512,
          Real.exp (-(k : ℝ) / (gammaMainCell7Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
            Real.sqrt (gammaMainCell7Scale : ℝ) := by
  apply
    gamma_gap_of_cell_caps (Finset.Ioc 0 512) (gammaMainCell7Scale : ℝ) L (gammaCell7Right : ℝ)
      (1817 / 100) (3830 / 100000) (gammaMainCell7Lower : ℝ) (18084000 / 1000000) (40197 / 10000)
      (by norm_num only [gammaMainCell7Scale, Rat.cast_div, Rat.cast_ofNat]) (by norm_num only)
      (by norm_num only [gammaMainCell7Scale, Rat.cast_div, Rat.cast_ofNat])
      (by norm_num only [gammaCell7Right, Rat.cast_div, Rat.cast_ofNat]) hL gammaCell7_power_upper
      gammaMainCell7_actual_lower
      (by simpa only [gammaUpperCell7Scale, gammaMainCell7Scale] using gammaCell7_principal_upper)
      gammaCell7_euler_lower (euler_mass_le_12372 hRH)
  norm_num only [gammaCell7Right, gammaMainCell7Scale, gammaMainCell7Lower, Rat.cast_div,
    Rat.cast_ofNat]

end PseudoPrime.PrimeTestBounds.MillerRabin
