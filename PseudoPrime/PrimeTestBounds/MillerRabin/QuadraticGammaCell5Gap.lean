/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaCell5Principal
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaSecondCellBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaMainCellBlock1

/-! # Certified scalar Gamma gap for cell 5 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The rational right endpoint of Gamma cell 5. -/
def gammaCell5Right : ℚ :=
  2574413363597 / 62500000000

/-- The checked Euler prefix through 503 exceeds the cell's rational cap.
Finite center-row verification supplies the lower estimate. -/
theorem gammaCell5_euler_lower :
    (40135 / 10000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 503, Analysis.gammaResolventMangoldtWeight n := by
  have hc :
    (40135 / 10000 : ℚ) ≤
      ((centerRowsBelow 503).map (fun r ↦ r.lo * Analysis.gammaFiniteEulerLower r.ratios)).sum := by
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using
    centerRowsBelow_euler_lower (by norm_num only : 503 ≤ 50000) (40135 / 10000) hc

/-- An integer-power comparison bounds the cell scale's negative `9/16`
power by the rational error cap. -/
theorem gammaCell5_power_upper : (gammaMainCell5Scale : ℝ) ^ (-9 / 16 : ℝ) ≤ 3863 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound
      (by norm_num only [gammaMainCell5Scale, Rat.cast_div, Rat.cast_ofNat]) (by norm_num only) 9 16
      (by decide)
  norm_num only [gammaMainCell5Scale, Rat.cast_div, Rat.cast_ofNat]

/-- Under RH, the principal, Euler and finite main-sum bounds give a strict
Gamma gap through the rational right endpoint of cell 5. -/
theorem gammaCell5_gap (hRH : RiemannHypothesis) {L : ℝ} (hL : L ≤ (gammaCell5Right : ℝ)) :
    (∑' k : ℕ,
              Real.exp (-(k : ℝ) / (gammaMainCell5Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
                Real.sqrt (gammaMainCell5Scale : ℝ)) +
            2 * (11783423 / 25000000 : ℝ) * L -
          477 / 100 +
        ((∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
          4 * ∑ k ∈ Finset.Ioc (0 : ℕ) 503, Analysis.gammaResolventMangoldtWeight k) +
        ((7 / 3 : ℝ) * L + 12) / Real.sqrt (gammaMainCell5Scale : ℝ) +
        (105 / 2 : ℝ) * (gammaMainCell5Scale : ℝ) ^ (-9 / 16 : ℝ) +
        3 / ((gammaMainCell5Scale : ℝ) * Real.sqrt (gammaMainCell5Scale : ℝ)) <
      4 *
        ∑ k ∈ Finset.Ioc (0 : ℕ) 503,
          Real.exp (-(k : ℝ) / (gammaMainCell5Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
            Real.sqrt (gammaMainCell5Scale : ℝ) := by
  apply
    gamma_gap_of_cell_caps (Finset.Ioc 0 503) (gammaMainCell5Scale : ℝ) L (gammaCell5Right : ℝ)
      (1803 / 100) (3863 / 100000) (gammaMainCell5Lower : ℝ) (17943237 / 1000000) (40135 / 10000)
      (by norm_num only [gammaMainCell5Scale, Rat.cast_div, Rat.cast_ofNat]) (by norm_num only)
      (by norm_num only [gammaMainCell5Scale, Rat.cast_div, Rat.cast_ofNat])
      (by norm_num only [gammaCell5Right, Rat.cast_div, Rat.cast_ofNat]) hL gammaCell5_power_upper
      gammaMainCell5_actual_lower
      (by simpa only [gammaUpperCell5Scale, gammaMainCell5Scale] using gammaCell5_principal_upper)
      gammaCell5_euler_lower (euler_mass_le_12372 hRH)
  norm_num only [gammaCell5Right, gammaMainCell5Scale, gammaMainCell5Lower, Rat.cast_div,
    Rat.cast_ofNat]

end PseudoPrime.PrimeTestBounds.MillerRabin
