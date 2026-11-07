/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaFixed92Main0
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaFixed92Power

/-! # Fixed-scale Gamma gaps across multiple cells -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The right endpoint reached by the fixed-scale cutoff 797. -/
def gammaFixed92Cell52Right : ℚ :=
  519294393063 / 10000000000

/-- The Euler prefix through 797 exceeds the rational lower cap.
The center-row certificate gives the finite sum comparison. -/
theorem gammaFixed92Cell52_euler_lower :
    (21071 / 5000 : ℝ) ≤ ∑ n ∈ Finset.Ioc (0 : ℕ) 797, Analysis.gammaResolventMangoldtWeight n := by
  have hc :
    (21071 / 5000 : ℚ) ≤
      ((centerRowsBelow 797).map (fun r ↦ r.lo * Analysis.gammaFiniteEulerLower r.ratios)).sum := by
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using
    centerRowsBelow_euler_lower (by norm_num only : 797 ≤ 50000) (21071 / 5000) hc

/-- Under RH, the fixed-scale principal, Euler and main bounds give a strict
Gamma gap up to the certified endpoint for cutoff 797. -/
theorem gammaFixed92Cell52_gap (hRH : RiemannHypothesis) {L : ℝ}
    (hL : L ≤ (gammaFixed92Cell52Right : ℝ)) :
    (∑' k : ℕ,
              Real.exp (-(k : ℝ) / (gammaMainCell92Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
                Real.sqrt (gammaMainCell92Scale : ℝ)) +
            2 * (11783423 / 25000000 : ℝ) * L -
          477 / 100 +
        ((∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
          4 * ∑ k ∈ Finset.Ioc (0 : ℕ) 797, Analysis.gammaResolventMangoldtWeight k) +
        ((7 / 3 : ℝ) * L + 12) / Real.sqrt (gammaMainCell92Scale : ℝ) +
        (105 / 2 : ℝ) * (gammaMainCell92Scale : ℝ) ^ (-9 / 16 : ℝ) +
        3 / ((gammaMainCell92Scale : ℝ) * Real.sqrt (gammaMainCell92Scale : ℝ)) <
      4 *
        ∑ k ∈ Finset.Ioc (0 : ℕ) 797,
          Real.exp (-(k : ℝ) / (gammaMainCell92Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
            Real.sqrt (gammaMainCell92Scale : ℝ) := by
  apply
    gamma_gap_of_cell_caps (Finset.Ioc 0 797) (gammaMainCell92Scale : ℝ) L
      (gammaFixed92Cell52Right : ℝ) (253 / 10) (33 / 1250) (gammaFixed92Main52Lower : ℝ)
      (25238049 / 1000000) (21071 / 5000)
      (by norm_num only [gammaMainCell92Scale, Rat.cast_div, Rat.cast_ofNat]) (by norm_num only)
      (by norm_num only [gammaMainCell92Scale, Rat.cast_div, Rat.cast_ofNat])
      (by norm_num only [gammaFixed92Cell52Right, Rat.cast_div, Rat.cast_ofNat]) hL
      gammaFixed92_power_upper gammaFixed92Main52_actual_lower
      (by
        simpa only [gammaUpperCell92Scale, gammaMainCell92Scale] using gammaCell92_principal_upper)
      gammaFixed92Cell52_euler_lower (euler_mass_le_12372 hRH)
  norm_num only [gammaFixed92Cell52Right, gammaMainCell92Scale, gammaFixed92Main52Lower,
    Rat.cast_div, Rat.cast_ofNat]

/-- The right endpoint reached by the fixed-scale cutoff 809. -/
def gammaFixed92Cell53Right : ℚ :=
  3249599334277 / 62500000000

/-- The Euler prefix through 809 exceeds the rational lower cap.
The center-row certificate gives the finite sum comparison. -/
theorem gammaFixed92Cell53_euler_lower :
    (21089 / 5000 : ℝ) ≤ ∑ n ∈ Finset.Ioc (0 : ℕ) 809, Analysis.gammaResolventMangoldtWeight n := by
  have hc :
    (21089 / 5000 : ℚ) ≤
      ((centerRowsBelow 809).map (fun r ↦ r.lo * Analysis.gammaFiniteEulerLower r.ratios)).sum := by
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using
    centerRowsBelow_euler_lower (by norm_num only : 809 ≤ 50000) (21089 / 5000) hc

/-- Under RH, the fixed-scale principal, Euler and main bounds give a strict
Gamma gap up to the certified endpoint for cutoff 809. -/
theorem gammaFixed92Cell53_gap (hRH : RiemannHypothesis) {L : ℝ}
    (hL : L ≤ (gammaFixed92Cell53Right : ℝ)) :
    (∑' k : ℕ,
              Real.exp (-(k : ℝ) / (gammaMainCell92Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
                Real.sqrt (gammaMainCell92Scale : ℝ)) +
            2 * (11783423 / 25000000 : ℝ) * L -
          477 / 100 +
        ((∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
          4 * ∑ k ∈ Finset.Ioc (0 : ℕ) 809, Analysis.gammaResolventMangoldtWeight k) +
        ((7 / 3 : ℝ) * L + 12) / Real.sqrt (gammaMainCell92Scale : ℝ) +
        (105 / 2 : ℝ) * (gammaMainCell92Scale : ℝ) ^ (-9 / 16 : ℝ) +
        3 / ((gammaMainCell92Scale : ℝ) * Real.sqrt (gammaMainCell92Scale : ℝ)) <
      4 *
        ∑ k ∈ Finset.Ioc (0 : ℕ) 809,
          Real.exp (-(k : ℝ) / (gammaMainCell92Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
            Real.sqrt (gammaMainCell92Scale : ℝ) := by
  apply
    gamma_gap_of_cell_caps (Finset.Ioc 0 809) (gammaMainCell92Scale : ℝ) L
      (gammaFixed92Cell53Right : ℝ) (253 / 10) (33 / 1250) (gammaFixed92Main53Lower : ℝ)
      (25238049 / 1000000) (21089 / 5000)
      (by norm_num only [gammaMainCell92Scale, Rat.cast_div, Rat.cast_ofNat]) (by norm_num only)
      (by norm_num only [gammaMainCell92Scale, Rat.cast_div, Rat.cast_ofNat])
      (by norm_num only [gammaFixed92Cell53Right, Rat.cast_div, Rat.cast_ofNat]) hL
      gammaFixed92_power_upper gammaFixed92Main53_actual_lower
      (by
        simpa only [gammaUpperCell92Scale, gammaMainCell92Scale] using gammaCell92_principal_upper)
      gammaFixed92Cell53_euler_lower (euler_mass_le_12372 hRH)
  norm_num only [gammaFixed92Cell53Right, gammaMainCell92Scale, gammaFixed92Main53Lower,
    Rat.cast_div, Rat.cast_ofNat]

/-- The right endpoint reached by the fixed-scale cutoff 811. -/
def gammaFixed92Cell54Right : ℚ :=
  13141854257803 / 250000000000

/-- The Euler prefix through 811 exceeds the rational lower cap.
The center-row certificate gives the finite sum comparison. -/
theorem gammaFixed92Cell54_euler_lower :
    (8443 / 2000 : ℝ) ≤ ∑ n ∈ Finset.Ioc (0 : ℕ) 811, Analysis.gammaResolventMangoldtWeight n := by
  have hc :
    (8443 / 2000 : ℚ) ≤
      ((centerRowsBelow 811).map (fun r ↦ r.lo * Analysis.gammaFiniteEulerLower r.ratios)).sum := by
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using
    centerRowsBelow_euler_lower (by norm_num only : 811 ≤ 50000) (8443 / 2000) hc

/-- Under RH, the fixed-scale principal, Euler and main bounds give a strict
Gamma gap up to the certified endpoint for cutoff 811. -/
theorem gammaFixed92Cell54_gap (hRH : RiemannHypothesis) {L : ℝ}
    (hL : L ≤ (gammaFixed92Cell54Right : ℝ)) :
    (∑' k : ℕ,
              Real.exp (-(k : ℝ) / (gammaMainCell92Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
                Real.sqrt (gammaMainCell92Scale : ℝ)) +
            2 * (11783423 / 25000000 : ℝ) * L -
          477 / 100 +
        ((∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
          4 * ∑ k ∈ Finset.Ioc (0 : ℕ) 811, Analysis.gammaResolventMangoldtWeight k) +
        ((7 / 3 : ℝ) * L + 12) / Real.sqrt (gammaMainCell92Scale : ℝ) +
        (105 / 2 : ℝ) * (gammaMainCell92Scale : ℝ) ^ (-9 / 16 : ℝ) +
        3 / ((gammaMainCell92Scale : ℝ) * Real.sqrt (gammaMainCell92Scale : ℝ)) <
      4 *
        ∑ k ∈ Finset.Ioc (0 : ℕ) 811,
          Real.exp (-(k : ℝ) / (gammaMainCell92Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
            Real.sqrt (gammaMainCell92Scale : ℝ) := by
  apply
    gamma_gap_of_cell_caps (Finset.Ioc 0 811) (gammaMainCell92Scale : ℝ) L
      (gammaFixed92Cell54Right : ℝ) (253 / 10) (33 / 1250) (gammaFixed92Main54Lower : ℝ)
      (25238049 / 1000000) (8443 / 2000)
      (by norm_num only [gammaMainCell92Scale, Rat.cast_div, Rat.cast_ofNat]) (by norm_num only)
      (by norm_num only [gammaMainCell92Scale, Rat.cast_div, Rat.cast_ofNat])
      (by norm_num only [gammaFixed92Cell54Right, Rat.cast_div, Rat.cast_ofNat]) hL
      gammaFixed92_power_upper gammaFixed92Main54_actual_lower
      (by
        simpa only [gammaUpperCell92Scale, gammaMainCell92Scale] using gammaCell92_principal_upper)
      gammaFixed92Cell54_euler_lower (euler_mass_le_12372 hRH)
  norm_num only [gammaFixed92Cell54Right, gammaMainCell92Scale, gammaFixed92Main54Lower,
    Rat.cast_div, Rat.cast_ofNat]

/-- The right endpoint reached by the fixed-scale cutoff 829. -/
def gammaFixed92Cell58Right : ℚ :=
  3352160373053 / 62500000000

/-- The Euler prefix through 829 exceeds the rational lower cap.
The center-row certificate gives the finite sum comparison. -/
theorem gammaFixed92Cell58_euler_lower :
    (42359 / 10000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 829, Analysis.gammaResolventMangoldtWeight n := by
  have hc :
    (42359 / 10000 : ℚ) ≤
      ((centerRowsBelow 829).map (fun r ↦ r.lo * Analysis.gammaFiniteEulerLower r.ratios)).sum := by
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using
    centerRowsBelow_euler_lower (by norm_num only : 829 ≤ 50000) (42359 / 10000) hc

/-- Under RH, the fixed-scale principal, Euler and main bounds give a strict
Gamma gap up to the certified endpoint for cutoff 829. -/
theorem gammaFixed92Cell58_gap (hRH : RiemannHypothesis) {L : ℝ}
    (hL : L ≤ (gammaFixed92Cell58Right : ℝ)) :
    (∑' k : ℕ,
              Real.exp (-(k : ℝ) / (gammaMainCell92Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
                Real.sqrt (gammaMainCell92Scale : ℝ)) +
            2 * (11783423 / 25000000 : ℝ) * L -
          477 / 100 +
        ((∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
          4 * ∑ k ∈ Finset.Ioc (0 : ℕ) 829, Analysis.gammaResolventMangoldtWeight k) +
        ((7 / 3 : ℝ) * L + 12) / Real.sqrt (gammaMainCell92Scale : ℝ) +
        (105 / 2 : ℝ) * (gammaMainCell92Scale : ℝ) ^ (-9 / 16 : ℝ) +
        3 / ((gammaMainCell92Scale : ℝ) * Real.sqrt (gammaMainCell92Scale : ℝ)) <
      4 *
        ∑ k ∈ Finset.Ioc (0 : ℕ) 829,
          Real.exp (-(k : ℝ) / (gammaMainCell92Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
            Real.sqrt (gammaMainCell92Scale : ℝ) := by
  apply
    gamma_gap_of_cell_caps (Finset.Ioc 0 829) (gammaMainCell92Scale : ℝ) L
      (gammaFixed92Cell58Right : ℝ) (253 / 10) (33 / 1250) (gammaFixed92Main58Lower : ℝ)
      (25238049 / 1000000) (42359 / 10000)
      (by norm_num only [gammaMainCell92Scale, Rat.cast_div, Rat.cast_ofNat]) (by norm_num only)
      (by norm_num only [gammaMainCell92Scale, Rat.cast_div, Rat.cast_ofNat])
      (by norm_num only [gammaFixed92Cell58Right, Rat.cast_div, Rat.cast_ofNat]) hL
      gammaFixed92_power_upper gammaFixed92Main58_actual_lower
      (by
        simpa only [gammaUpperCell92Scale, gammaMainCell92Scale] using gammaCell92_principal_upper)
      gammaFixed92Cell58_euler_lower (euler_mass_le_12372 hRH)
  norm_num only [gammaFixed92Cell58Right, gammaMainCell92Scale, gammaFixed92Main58Lower,
    Rat.cast_div, Rat.cast_ofNat]

/-- The right endpoint reached by the fixed-scale cutoff 863. -/
def gammaFixed92Cell64Right : ℚ :=
  13836846943337 / 250000000000

/-- The Euler prefix through 863 exceeds the rational lower cap.
The center-row certificate gives the finite sum comparison. -/
theorem gammaFixed92Cell64_euler_lower :
    (42551 / 10000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 863, Analysis.gammaResolventMangoldtWeight n := by
  have hc :
    (42551 / 10000 : ℚ) ≤
      ((centerRowsBelow 863).map (fun r ↦ r.lo * Analysis.gammaFiniteEulerLower r.ratios)).sum := by
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using
    centerRowsBelow_euler_lower (by norm_num only : 863 ≤ 50000) (42551 / 10000) hc

/-- Under RH, the fixed-scale principal, Euler and main bounds give a strict
Gamma gap up to the certified endpoint for cutoff 863. -/
theorem gammaFixed92Cell64_gap (hRH : RiemannHypothesis) {L : ℝ}
    (hL : L ≤ (gammaFixed92Cell64Right : ℝ)) :
    (∑' k : ℕ,
              Real.exp (-(k : ℝ) / (gammaMainCell92Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
                Real.sqrt (gammaMainCell92Scale : ℝ)) +
            2 * (11783423 / 25000000 : ℝ) * L -
          477 / 100 +
        ((∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
          4 * ∑ k ∈ Finset.Ioc (0 : ℕ) 863, Analysis.gammaResolventMangoldtWeight k) +
        ((7 / 3 : ℝ) * L + 12) / Real.sqrt (gammaMainCell92Scale : ℝ) +
        (105 / 2 : ℝ) * (gammaMainCell92Scale : ℝ) ^ (-9 / 16 : ℝ) +
        3 / ((gammaMainCell92Scale : ℝ) * Real.sqrt (gammaMainCell92Scale : ℝ)) <
      4 *
        ∑ k ∈ Finset.Ioc (0 : ℕ) 863,
          Real.exp (-(k : ℝ) / (gammaMainCell92Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
            Real.sqrt (gammaMainCell92Scale : ℝ) := by
  apply
    gamma_gap_of_cell_caps (Finset.Ioc 0 863) (gammaMainCell92Scale : ℝ) L
      (gammaFixed92Cell64Right : ℝ) (253 / 10) (33 / 1250) (gammaFixed92Main64Lower : ℝ)
      (25238049 / 1000000) (42551 / 10000)
      (by norm_num only [gammaMainCell92Scale, Rat.cast_div, Rat.cast_ofNat]) (by norm_num only)
      (by norm_num only [gammaMainCell92Scale, Rat.cast_div, Rat.cast_ofNat])
      (by norm_num only [gammaFixed92Cell64Right, Rat.cast_div, Rat.cast_ofNat]) hL
      gammaFixed92_power_upper gammaFixed92Main64_actual_lower
      (by
        simpa only [gammaUpperCell92Scale, gammaMainCell92Scale] using gammaCell92_principal_upper)
      gammaFixed92Cell64_euler_lower (euler_mass_le_12372 hRH)
  norm_num only [gammaFixed92Cell64Right, gammaMainCell92Scale, gammaFixed92Main64Lower,
    Rat.cast_div, Rat.cast_ofNat]

end PseudoPrime.PrimeTestBounds.MillerRabin
