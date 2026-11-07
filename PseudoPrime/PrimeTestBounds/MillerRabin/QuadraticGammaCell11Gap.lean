/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaCell11Principal
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaSecondCellBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaMainCellBlock9

/-! # Certified scalar Gamma gap for cell 11 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The rational right endpoint of Gamma cell 11. -/
def gammaCell11Right : ℚ :=
  42700507413067 / 1000000000000

/-- The checked Euler prefix through 541 exceeds the cell's rational cap.
Finite center-row verification supplies the lower estimate. -/
theorem gammaCell11_euler_lower :
    (40388 / 10000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 541, Analysis.gammaResolventMangoldtWeight n := by
  have hc :
    (40388 / 10000 : ℚ) ≤
      ((centerRowsBelow 541).map (fun r ↦ r.lo * Analysis.gammaFiniteEulerLower r.ratios)).sum := by
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using
    centerRowsBelow_euler_lower (by norm_num only : 541 ≤ 50000) (40388 / 10000) hc

/-- An integer-power comparison bounds the cell scale's negative `9/16`
power by the rational error cap. -/
theorem gammaCell11_power_upper : (gammaMainCell11Scale : ℝ) ^ (-9 / 16 : ℝ) ≤ 3723 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound
      (by norm_num only [gammaMainCell11Scale, Rat.cast_div, Rat.cast_ofNat]) (by norm_num only) 9
      16 (by decide)
  norm_num only [gammaMainCell11Scale, Rat.cast_div, Rat.cast_ofNat]

/-- Under RH, the principal, Euler and finite main-sum bounds give a strict
Gamma gap through the rational right endpoint of cell 11. -/
theorem gammaCell11_gap (hRH : RiemannHypothesis) {L : ℝ} (hL : L ≤ (gammaCell11Right : ℝ)) :
    (∑' k : ℕ,
              Real.exp (-(k : ℝ) / (gammaMainCell11Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
                Real.sqrt (gammaMainCell11Scale : ℝ)) +
            2 * (11783423 / 25000000 : ℝ) * L -
          477 / 100 +
        ((∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
          4 * ∑ k ∈ Finset.Ioc (0 : ℕ) 541, Analysis.gammaResolventMangoldtWeight k) +
        ((7 / 3 : ℝ) * L + 12) / Real.sqrt (gammaMainCell11Scale : ℝ) +
        (105 / 2 : ℝ) * (gammaMainCell11Scale : ℝ) ^ (-9 / 16 : ℝ) +
        3 / ((gammaMainCell11Scale : ℝ) * Real.sqrt (gammaMainCell11Scale : ℝ)) <
      4 *
        ∑ k ∈ Finset.Ioc (0 : ℕ) 541,
          Real.exp (-(k : ℝ) / (gammaMainCell11Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
            Real.sqrt (gammaMainCell11Scale : ℝ) := by
  apply
    gamma_gap_of_cell_caps (Finset.Ioc 0 541) (gammaMainCell11Scale : ℝ) L (gammaCell11Right : ℝ)
      (1863 / 100) (3723 / 100000) (gammaMainCell11Lower : ℝ) (18550790 / 1000000) (40388 / 10000)
      (by norm_num only [gammaMainCell11Scale, Rat.cast_div, Rat.cast_ofNat]) (by norm_num only)
      (by norm_num only [gammaMainCell11Scale, Rat.cast_div, Rat.cast_ofNat])
      (by norm_num only [gammaCell11Right, Rat.cast_div, Rat.cast_ofNat]) hL gammaCell11_power_upper
      gammaMainCell11_actual_lower
      (by
        simpa only [gammaUpperCell11Scale, gammaMainCell11Scale] using gammaCell11_principal_upper)
      gammaCell11_euler_lower (euler_mass_le_12372 hRH)
  norm_num only [gammaCell11Right, gammaMainCell11Scale, gammaMainCell11Lower, Rat.cast_div,
    Rat.cast_ofNat]

end PseudoPrime.PrimeTestBounds.MillerRabin
