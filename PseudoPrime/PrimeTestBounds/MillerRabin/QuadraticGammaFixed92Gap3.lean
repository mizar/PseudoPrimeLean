/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaFixed92Main3
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaFixed92Power

/-! # Fixed-scale Gamma gaps across multiple cells -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The right endpoint reached by the fixed-scale cutoff 1609. -/
def gammaFixed92Cell172Right : ℚ :=
  73643284373617 / 1000000000000

/-- The Euler prefix through 1609 exceeds the rational lower cap.
The center-row certificate gives the finite sum comparison. -/
theorem gammaFixed92Cell172_euler_lower :
    (2826 / 625 : ℝ) ≤ ∑ n ∈ Finset.Ioc (0 : ℕ) 1609, Analysis.gammaResolventMangoldtWeight n := by
  have hc :
    (2826 / 625 : ℚ) ≤
      ((centerRowsBelow 1609).map
          (fun r ↦ r.lo * Analysis.gammaFiniteEulerLower r.ratios)).sum := by
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using
    centerRowsBelow_euler_lower (by norm_num only : 1609 ≤ 50000) (2826 / 625) hc

/-- Under RH, the fixed-scale principal, Euler and main bounds give a strict
Gamma gap up to the certified endpoint for cutoff 1609. -/
theorem gammaFixed92Cell172_gap (hRH : RiemannHypothesis) {L : ℝ}
    (hL : L ≤ (gammaFixed92Cell172Right : ℝ)) :
    (∑' k : ℕ,
              Real.exp (-(k : ℝ) / (gammaMainCell92Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
                Real.sqrt (gammaMainCell92Scale : ℝ)) +
            2 * (11783423 / 25000000 : ℝ) * L -
          477 / 100 +
        ((∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
          4 * ∑ k ∈ Finset.Ioc (0 : ℕ) 1609, Analysis.gammaResolventMangoldtWeight k) +
        ((7 / 3 : ℝ) * L + 12) / Real.sqrt (gammaMainCell92Scale : ℝ) +
        (105 / 2 : ℝ) * (gammaMainCell92Scale : ℝ) ^ (-9 / 16 : ℝ) +
        3 / ((gammaMainCell92Scale : ℝ) * Real.sqrt (gammaMainCell92Scale : ℝ)) <
      4 *
        ∑ k ∈ Finset.Ioc (0 : ℕ) 1609,
          Real.exp (-(k : ℝ) / (gammaMainCell92Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
            Real.sqrt (gammaMainCell92Scale : ℝ) := by
  apply
    gamma_gap_of_cell_caps (Finset.Ioc 0 1609) (gammaMainCell92Scale : ℝ) L
      (gammaFixed92Cell172Right : ℝ) (253 / 10) (33 / 1250) (gammaFixed92Main172Lower : ℝ)
      (25238049 / 1000000) (2826 / 625)
      (by norm_num only [gammaMainCell92Scale, Rat.cast_div, Rat.cast_ofNat]) (by norm_num only)
      (by norm_num only [gammaMainCell92Scale, Rat.cast_div, Rat.cast_ofNat])
      (by norm_num only [gammaFixed92Cell172Right, Rat.cast_div, Rat.cast_ofNat]) hL
      gammaFixed92_power_upper gammaFixed92Main172_actual_lower
      (by
        simpa only [gammaUpperCell92Scale, gammaMainCell92Scale] using gammaCell92_principal_upper)
      gammaFixed92Cell172_euler_lower (euler_mass_le_12372 hRH)
  norm_num only [gammaFixed92Cell172Right, gammaMainCell92Scale, gammaFixed92Main172Lower,
    Rat.cast_div, Rat.cast_ofNat]

/-- The right endpoint reached by the fixed-scale cutoff 1627. -/
def gammaFixed92Cell176Right : ℚ :=
  73869253865643 / 1000000000000

/-- The Euler prefix through 1627 exceeds the rational lower cap.
The center-row certificate gives the finite sum comparison. -/
theorem gammaFixed92Cell176_euler_lower :
    (45293 / 10000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 1627, Analysis.gammaResolventMangoldtWeight n := by
  have hc :
    (45293 / 10000 : ℚ) ≤
      ((centerRowsBelow 1627).map
          (fun r ↦ r.lo * Analysis.gammaFiniteEulerLower r.ratios)).sum := by
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using
    centerRowsBelow_euler_lower (by norm_num only : 1627 ≤ 50000) (45293 / 10000) hc

/-- Under RH, the fixed-scale principal, Euler and main bounds give a strict
Gamma gap up to the certified endpoint for cutoff 1627. -/
theorem gammaFixed92Cell176_gap (hRH : RiemannHypothesis) {L : ℝ}
    (hL : L ≤ (gammaFixed92Cell176Right : ℝ)) :
    (∑' k : ℕ,
              Real.exp (-(k : ℝ) / (gammaMainCell92Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
                Real.sqrt (gammaMainCell92Scale : ℝ)) +
            2 * (11783423 / 25000000 : ℝ) * L -
          477 / 100 +
        ((∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
          4 * ∑ k ∈ Finset.Ioc (0 : ℕ) 1627, Analysis.gammaResolventMangoldtWeight k) +
        ((7 / 3 : ℝ) * L + 12) / Real.sqrt (gammaMainCell92Scale : ℝ) +
        (105 / 2 : ℝ) * (gammaMainCell92Scale : ℝ) ^ (-9 / 16 : ℝ) +
        3 / ((gammaMainCell92Scale : ℝ) * Real.sqrt (gammaMainCell92Scale : ℝ)) <
      4 *
        ∑ k ∈ Finset.Ioc (0 : ℕ) 1627,
          Real.exp (-(k : ℝ) / (gammaMainCell92Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
            Real.sqrt (gammaMainCell92Scale : ℝ) := by
  apply
    gamma_gap_of_cell_caps (Finset.Ioc 0 1627) (gammaMainCell92Scale : ℝ) L
      (gammaFixed92Cell176Right : ℝ) (253 / 10) (33 / 1250) (gammaFixed92Main176Lower : ℝ)
      (25238049 / 1000000) (45293 / 10000)
      (by norm_num only [gammaMainCell92Scale, Rat.cast_div, Rat.cast_ofNat]) (by norm_num only)
      (by norm_num only [gammaMainCell92Scale, Rat.cast_div, Rat.cast_ofNat])
      (by norm_num only [gammaFixed92Cell176Right, Rat.cast_div, Rat.cast_ofNat]) hL
      gammaFixed92_power_upper gammaFixed92Main176_actual_lower
      (by
        simpa only [gammaUpperCell92Scale, gammaMainCell92Scale] using gammaCell92_principal_upper)
      gammaFixed92Cell176_euler_lower (euler_mass_le_12372 hRH)
  norm_num only [gammaFixed92Cell176Right, gammaMainCell92Scale, gammaFixed92Main176Lower,
    Rat.cast_div, Rat.cast_ofNat]

end PseudoPrime.PrimeTestBounds.MillerRabin
