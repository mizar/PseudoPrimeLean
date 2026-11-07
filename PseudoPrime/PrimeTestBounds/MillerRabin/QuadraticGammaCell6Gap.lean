/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaCell6Principal
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaSecondCellBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaMainCellBlock1

/-! # Certified scalar Gamma gap for cell 6 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The rational right endpoint of Gamma cell 6. -/
def gammaCell6Right : ℚ :=
  20655911179773 / 500000000000

/-- The checked Euler prefix through 509 exceeds the cell's rational cap.
Finite center-row verification supplies the lower estimate. -/
theorem gammaCell6_euler_lower :
    (40191 / 10000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 509, Analysis.gammaResolventMangoldtWeight n := by
  have hc :
    (40191 / 10000 : ℚ) ≤
      ((centerRowsBelow 509).map (fun r ↦ r.lo * Analysis.gammaFiniteEulerLower r.ratios)).sum := by
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using
    centerRowsBelow_euler_lower (by norm_num only : 509 ≤ 50000) (40191 / 10000) hc

/-- An integer-power comparison bounds the cell scale's negative `9/16`
power by the rational error cap. -/
theorem gammaCell6_power_upper : (gammaMainCell6Scale : ℝ) ^ (-9 / 16 : ℝ) ≤ 3839 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound
      (by norm_num only [gammaMainCell6Scale, Rat.cast_div, Rat.cast_ofNat]) (by norm_num only) 9 16
      (by decide)
  norm_num only [gammaMainCell6Scale, Rat.cast_div, Rat.cast_ofNat]

/-- Under RH, the principal, Euler and finite main-sum bounds give a strict
Gamma gap through the rational right endpoint of cell 6. -/
theorem gammaCell6_gap (hRH : RiemannHypothesis) {L : ℝ} (hL : L ≤ (gammaCell6Right : ℝ)) :
    (∑' k : ℕ,
              Real.exp (-(k : ℝ) / (gammaMainCell6Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
                Real.sqrt (gammaMainCell6Scale : ℝ)) +
            2 * (11783423 / 25000000 : ℝ) * L -
          477 / 100 +
        ((∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
          4 * ∑ k ∈ Finset.Ioc (0 : ℕ) 509, Analysis.gammaResolventMangoldtWeight k) +
        ((7 / 3 : ℝ) * L + 12) / Real.sqrt (gammaMainCell6Scale : ℝ) +
        (105 / 2 : ℝ) * (gammaMainCell6Scale : ℝ) ^ (-9 / 16 : ℝ) +
        3 / ((gammaMainCell6Scale : ℝ) * Real.sqrt (gammaMainCell6Scale : ℝ)) <
      4 *
        ∑ k ∈ Finset.Ioc (0 : ℕ) 509,
          Real.exp (-(k : ℝ) / (gammaMainCell6Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
            Real.sqrt (gammaMainCell6Scale : ℝ) := by
  apply
    gamma_gap_of_cell_caps (Finset.Ioc 0 509) (gammaMainCell6Scale : ℝ) L (gammaCell6Right : ℝ)
      (1813 / 100) (3839 / 100000) (gammaMainCell6Lower : ℝ) (18045829 / 1000000) (40191 / 10000)
      (by norm_num only [gammaMainCell6Scale, Rat.cast_div, Rat.cast_ofNat]) (by norm_num only)
      (by norm_num only [gammaMainCell6Scale, Rat.cast_div, Rat.cast_ofNat])
      (by norm_num only [gammaCell6Right, Rat.cast_div, Rat.cast_ofNat]) hL gammaCell6_power_upper
      gammaMainCell6_actual_lower
      (by simpa only [gammaUpperCell6Scale, gammaMainCell6Scale] using gammaCell6_principal_upper)
      gammaCell6_euler_lower (euler_mass_le_12372 hRH)
  norm_num only [gammaCell6Right, gammaMainCell6Scale, gammaMainCell6Lower, Rat.cast_div,
    Rat.cast_ofNat]

end PseudoPrime.PrimeTestBounds.MillerRabin
