/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaFixed92Main1
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaFixed92Power

/-! # Fixed-scale Gamma gaps across multiple cells -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The right endpoint reached by the fixed-scale cutoff 919. -/
def gammaFixed92Cell71Right : ℚ :=
  57067211835403 / 1000000000000

/-- The Euler prefix through 919 exceeds the rational lower cap.
The center-row certificate gives the finite sum comparison. -/
theorem gammaFixed92Cell71_euler_lower :
    (8557 / 2000 : ℝ) ≤ ∑ n ∈ Finset.Ioc (0 : ℕ) 919, Analysis.gammaResolventMangoldtWeight n := by
  have hc :
    (8557 / 2000 : ℚ) ≤
      ((centerRowsBelow 919).map (fun r ↦ r.lo * Analysis.gammaFiniteEulerLower r.ratios)).sum := by
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using
    centerRowsBelow_euler_lower (by norm_num only : 919 ≤ 50000) (8557 / 2000) hc

/-- Under RH, the fixed-scale principal, Euler and main bounds give a strict
Gamma gap up to the certified endpoint for cutoff 919. -/
theorem gammaFixed92Cell71_gap (hRH : RiemannHypothesis) {L : ℝ}
    (hL : L ≤ (gammaFixed92Cell71Right : ℝ)) :
    (∑' k : ℕ,
              Real.exp (-(k : ℝ) / (gammaMainCell92Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
                Real.sqrt (gammaMainCell92Scale : ℝ)) +
            2 * (11783423 / 25000000 : ℝ) * L -
          477 / 100 +
        ((∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
          4 * ∑ k ∈ Finset.Ioc (0 : ℕ) 919, Analysis.gammaResolventMangoldtWeight k) +
        ((7 / 3 : ℝ) * L + 12) / Real.sqrt (gammaMainCell92Scale : ℝ) +
        (105 / 2 : ℝ) * (gammaMainCell92Scale : ℝ) ^ (-9 / 16 : ℝ) +
        3 / ((gammaMainCell92Scale : ℝ) * Real.sqrt (gammaMainCell92Scale : ℝ)) <
      4 *
        ∑ k ∈ Finset.Ioc (0 : ℕ) 919,
          Real.exp (-(k : ℝ) / (gammaMainCell92Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
            Real.sqrt (gammaMainCell92Scale : ℝ) := by
  apply
    gamma_gap_of_cell_caps (Finset.Ioc 0 919) (gammaMainCell92Scale : ℝ) L
      (gammaFixed92Cell71Right : ℝ) (253 / 10) (33 / 1250) (gammaFixed92Main71Lower : ℝ)
      (25238049 / 1000000) (8557 / 2000)
      (by norm_num only [gammaMainCell92Scale, Rat.cast_div, Rat.cast_ofNat]) (by norm_num only)
      (by norm_num only [gammaMainCell92Scale, Rat.cast_div, Rat.cast_ofNat])
      (by norm_num only [gammaFixed92Cell71Right, Rat.cast_div, Rat.cast_ofNat]) hL
      gammaFixed92_power_upper gammaFixed92Main71_actual_lower
      (by
        simpa only [gammaUpperCell92Scale, gammaMainCell92Scale] using gammaCell92_principal_upper)
      gammaFixed92Cell71_euler_lower (euler_mass_le_12372 hRH)
  norm_num only [gammaFixed92Cell71Right, gammaMainCell92Scale, gammaFixed92Main71Lower,
    Rat.cast_div, Rat.cast_ofNat]

/-- The right endpoint reached by the fixed-scale cutoff 977. -/
def gammaFixed92Cell80Right : ℚ :=
  29594481467553 / 500000000000

/-- The Euler prefix through 977 exceeds the rational lower cap.
The center-row certificate gives the finite sum comparison. -/
theorem gammaFixed92Cell80_euler_lower :
    (10763 / 2500 : ℝ) ≤ ∑ n ∈ Finset.Ioc (0 : ℕ) 977, Analysis.gammaResolventMangoldtWeight n := by
  have hc :
    (10763 / 2500 : ℚ) ≤
      ((centerRowsBelow 977).map (fun r ↦ r.lo * Analysis.gammaFiniteEulerLower r.ratios)).sum := by
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using
    centerRowsBelow_euler_lower (by norm_num only : 977 ≤ 50000) (10763 / 2500) hc

/-- Under RH, the fixed-scale principal, Euler and main bounds give a strict
Gamma gap up to the certified endpoint for cutoff 977. -/
theorem gammaFixed92Cell80_gap (hRH : RiemannHypothesis) {L : ℝ}
    (hL : L ≤ (gammaFixed92Cell80Right : ℝ)) :
    (∑' k : ℕ,
              Real.exp (-(k : ℝ) / (gammaMainCell92Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
                Real.sqrt (gammaMainCell92Scale : ℝ)) +
            2 * (11783423 / 25000000 : ℝ) * L -
          477 / 100 +
        ((∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
          4 * ∑ k ∈ Finset.Ioc (0 : ℕ) 977, Analysis.gammaResolventMangoldtWeight k) +
        ((7 / 3 : ℝ) * L + 12) / Real.sqrt (gammaMainCell92Scale : ℝ) +
        (105 / 2 : ℝ) * (gammaMainCell92Scale : ℝ) ^ (-9 / 16 : ℝ) +
        3 / ((gammaMainCell92Scale : ℝ) * Real.sqrt (gammaMainCell92Scale : ℝ)) <
      4 *
        ∑ k ∈ Finset.Ioc (0 : ℕ) 977,
          Real.exp (-(k : ℝ) / (gammaMainCell92Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
            Real.sqrt (gammaMainCell92Scale : ℝ) := by
  apply
    gamma_gap_of_cell_caps (Finset.Ioc 0 977) (gammaMainCell92Scale : ℝ) L
      (gammaFixed92Cell80Right : ℝ) (253 / 10) (33 / 1250) (gammaFixed92Main80Lower : ℝ)
      (25238049 / 1000000) (10763 / 2500)
      (by norm_num only [gammaMainCell92Scale, Rat.cast_div, Rat.cast_ofNat]) (by norm_num only)
      (by norm_num only [gammaMainCell92Scale, Rat.cast_div, Rat.cast_ofNat])
      (by norm_num only [gammaFixed92Cell80Right, Rat.cast_div, Rat.cast_ofNat]) hL
      gammaFixed92_power_upper gammaFixed92Main80_actual_lower
      (by
        simpa only [gammaUpperCell92Scale, gammaMainCell92Scale] using gammaCell92_principal_upper)
      gammaFixed92Cell80_euler_lower (euler_mass_le_12372 hRH)
  norm_num only [gammaFixed92Cell80Right, gammaMainCell92Scale, gammaFixed92Main80Lower,
    Rat.cast_div, Rat.cast_ofNat]

/-- The right endpoint reached by the fixed-scale cutoff 1051. -/
def gammaFixed92Cell93Right : ℚ :=
  61994623422789 / 1000000000000

/-- The Euler prefix through 1051 exceeds the rational lower cap.
The center-row certificate gives the finite sum comparison. -/
theorem gammaFixed92Cell93_euler_lower :
    (4341 / 1000 : ℝ) ≤ ∑ n ∈ Finset.Ioc (0 : ℕ) 1051, Analysis.gammaResolventMangoldtWeight n := by
  have hc :
    (4341 / 1000 : ℚ) ≤
      ((centerRowsBelow 1051).map
          (fun r ↦ r.lo * Analysis.gammaFiniteEulerLower r.ratios)).sum := by
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using
    centerRowsBelow_euler_lower (by norm_num only : 1051 ≤ 50000) (4341 / 1000) hc

/-- Under RH, the fixed-scale principal, Euler and main bounds give a strict
Gamma gap up to the certified endpoint for cutoff 1051. -/
theorem gammaFixed92Cell93_gap (hRH : RiemannHypothesis) {L : ℝ}
    (hL : L ≤ (gammaFixed92Cell93Right : ℝ)) :
    (∑' k : ℕ,
              Real.exp (-(k : ℝ) / (gammaMainCell92Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
                Real.sqrt (gammaMainCell92Scale : ℝ)) +
            2 * (11783423 / 25000000 : ℝ) * L -
          477 / 100 +
        ((∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
          4 * ∑ k ∈ Finset.Ioc (0 : ℕ) 1051, Analysis.gammaResolventMangoldtWeight k) +
        ((7 / 3 : ℝ) * L + 12) / Real.sqrt (gammaMainCell92Scale : ℝ) +
        (105 / 2 : ℝ) * (gammaMainCell92Scale : ℝ) ^ (-9 / 16 : ℝ) +
        3 / ((gammaMainCell92Scale : ℝ) * Real.sqrt (gammaMainCell92Scale : ℝ)) <
      4 *
        ∑ k ∈ Finset.Ioc (0 : ℕ) 1051,
          Real.exp (-(k : ℝ) / (gammaMainCell92Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
            Real.sqrt (gammaMainCell92Scale : ℝ) := by
  apply
    gamma_gap_of_cell_caps (Finset.Ioc 0 1051) (gammaMainCell92Scale : ℝ) L
      (gammaFixed92Cell93Right : ℝ) (253 / 10) (33 / 1250) (gammaFixed92Main93Lower : ℝ)
      (25238049 / 1000000) (4341 / 1000)
      (by norm_num only [gammaMainCell92Scale, Rat.cast_div, Rat.cast_ofNat]) (by norm_num only)
      (by norm_num only [gammaMainCell92Scale, Rat.cast_div, Rat.cast_ofNat])
      (by norm_num only [gammaFixed92Cell93Right, Rat.cast_div, Rat.cast_ofNat]) hL
      gammaFixed92_power_upper gammaFixed92Main93_actual_lower
      (by
        simpa only [gammaUpperCell92Scale, gammaMainCell92Scale] using gammaCell92_principal_upper)
      gammaFixed92Cell93_euler_lower (euler_mass_le_12372 hRH)
  norm_num only [gammaFixed92Cell93Right, gammaMainCell92Scale, gammaFixed92Main93Lower,
    Rat.cast_div, Rat.cast_ofNat]

/-- The right endpoint reached by the fixed-scale cutoff 1153. -/
def gammaFixed92Cell107Right : ℚ :=
  16195421163609 / 250000000000

/-- The Euler prefix through 1153 exceeds the rational lower cap.
The center-row certificate gives the finite sum comparison. -/
theorem gammaFixed92Cell107_euler_lower :
    (8759 / 2000 : ℝ) ≤ ∑ n ∈ Finset.Ioc (0 : ℕ) 1153, Analysis.gammaResolventMangoldtWeight n := by
  have hc :
    (8759 / 2000 : ℚ) ≤
      ((centerRowsBelow 1153).map
          (fun r ↦ r.lo * Analysis.gammaFiniteEulerLower r.ratios)).sum := by
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using
    centerRowsBelow_euler_lower (by norm_num only : 1153 ≤ 50000) (8759 / 2000) hc

/-- Under RH, the fixed-scale principal, Euler and main bounds give a strict
Gamma gap up to the certified endpoint for cutoff 1153. -/
theorem gammaFixed92Cell107_gap (hRH : RiemannHypothesis) {L : ℝ}
    (hL : L ≤ (gammaFixed92Cell107Right : ℝ)) :
    (∑' k : ℕ,
              Real.exp (-(k : ℝ) / (gammaMainCell92Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
                Real.sqrt (gammaMainCell92Scale : ℝ)) +
            2 * (11783423 / 25000000 : ℝ) * L -
          477 / 100 +
        ((∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
          4 * ∑ k ∈ Finset.Ioc (0 : ℕ) 1153, Analysis.gammaResolventMangoldtWeight k) +
        ((7 / 3 : ℝ) * L + 12) / Real.sqrt (gammaMainCell92Scale : ℝ) +
        (105 / 2 : ℝ) * (gammaMainCell92Scale : ℝ) ^ (-9 / 16 : ℝ) +
        3 / ((gammaMainCell92Scale : ℝ) * Real.sqrt (gammaMainCell92Scale : ℝ)) <
      4 *
        ∑ k ∈ Finset.Ioc (0 : ℕ) 1153,
          Real.exp (-(k : ℝ) / (gammaMainCell92Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
            Real.sqrt (gammaMainCell92Scale : ℝ) := by
  apply
    gamma_gap_of_cell_caps (Finset.Ioc 0 1153) (gammaMainCell92Scale : ℝ) L
      (gammaFixed92Cell107Right : ℝ) (253 / 10) (33 / 1250) (gammaFixed92Main107Lower : ℝ)
      (25238049 / 1000000) (8759 / 2000)
      (by norm_num only [gammaMainCell92Scale, Rat.cast_div, Rat.cast_ofNat]) (by norm_num only)
      (by norm_num only [gammaMainCell92Scale, Rat.cast_div, Rat.cast_ofNat])
      (by norm_num only [gammaFixed92Cell107Right, Rat.cast_div, Rat.cast_ofNat]) hL
      gammaFixed92_power_upper gammaFixed92Main107_actual_lower
      (by
        simpa only [gammaUpperCell92Scale, gammaMainCell92Scale] using gammaCell92_principal_upper)
      gammaFixed92Cell107_euler_lower (euler_mass_le_12372 hRH)
  norm_num only [gammaFixed92Cell107Right, gammaMainCell92Scale, gammaFixed92Main107Lower,
    Rat.cast_div, Rat.cast_ofNat]

/-- The right endpoint reached by the fixed-scale cutoff 1259. -/
def gammaFixed92Cell121Right : ℚ :=
  13321661558029 / 200000000000

/-- The Euler prefix through 1259 exceeds the rational lower cap.
The center-row certificate gives the finite sum comparison. -/
theorem gammaFixed92Cell121_euler_lower :
    (44147 / 10000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 1259, Analysis.gammaResolventMangoldtWeight n := by
  have hc :
    (44147 / 10000 : ℚ) ≤
      ((centerRowsBelow 1259).map
          (fun r ↦ r.lo * Analysis.gammaFiniteEulerLower r.ratios)).sum := by
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using
    centerRowsBelow_euler_lower (by norm_num only : 1259 ≤ 50000) (44147 / 10000) hc

/-- Under RH, the fixed-scale principal, Euler and main bounds give a strict
Gamma gap up to the certified endpoint for cutoff 1259. -/
theorem gammaFixed92Cell121_gap (hRH : RiemannHypothesis) {L : ℝ}
    (hL : L ≤ (gammaFixed92Cell121Right : ℝ)) :
    (∑' k : ℕ,
              Real.exp (-(k : ℝ) / (gammaMainCell92Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
                Real.sqrt (gammaMainCell92Scale : ℝ)) +
            2 * (11783423 / 25000000 : ℝ) * L -
          477 / 100 +
        ((∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
          4 * ∑ k ∈ Finset.Ioc (0 : ℕ) 1259, Analysis.gammaResolventMangoldtWeight k) +
        ((7 / 3 : ℝ) * L + 12) / Real.sqrt (gammaMainCell92Scale : ℝ) +
        (105 / 2 : ℝ) * (gammaMainCell92Scale : ℝ) ^ (-9 / 16 : ℝ) +
        3 / ((gammaMainCell92Scale : ℝ) * Real.sqrt (gammaMainCell92Scale : ℝ)) <
      4 *
        ∑ k ∈ Finset.Ioc (0 : ℕ) 1259,
          Real.exp (-(k : ℝ) / (gammaMainCell92Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
            Real.sqrt (gammaMainCell92Scale : ℝ) := by
  apply
    gamma_gap_of_cell_caps (Finset.Ioc 0 1259) (gammaMainCell92Scale : ℝ) L
      (gammaFixed92Cell121Right : ℝ) (253 / 10) (33 / 1250) (gammaFixed92Main121Lower : ℝ)
      (25238049 / 1000000) (44147 / 10000)
      (by norm_num only [gammaMainCell92Scale, Rat.cast_div, Rat.cast_ofNat]) (by norm_num only)
      (by norm_num only [gammaMainCell92Scale, Rat.cast_div, Rat.cast_ofNat])
      (by norm_num only [gammaFixed92Cell121Right, Rat.cast_div, Rat.cast_ofNat]) hL
      gammaFixed92_power_upper gammaFixed92Main121_actual_lower
      (by
        simpa only [gammaUpperCell92Scale, gammaMainCell92Scale] using gammaCell92_principal_upper)
      gammaFixed92Cell121_euler_lower (euler_mass_le_12372 hRH)
  norm_num only [gammaFixed92Cell121Right, gammaMainCell92Scale, gammaFixed92Main121Lower,
    Rat.cast_div, Rat.cast_ofNat]

end PseudoPrime.PrimeTestBounds.MillerRabin
