/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaFixed17Main0
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaFixed17Main1

/-! # Fixed-scale Gamma gaps across multiple cells -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The right endpoint reached by the fixed-scale cutoff 587. -/
def gammaFixed17Cell18Right : ℚ :=
  22379305917149 / 500000000000

/-- The Euler prefix through 587 exceeds the rational lower cap.
The center-row certificate gives the finite sum comparison. -/
theorem gammaFixed17Cell18_euler_lower :
    (20373 / 5000 : ℝ) ≤ ∑ n ∈ Finset.Ioc (0 : ℕ) 587, Analysis.gammaResolventMangoldtWeight n := by
  have hc :
    (20373 / 5000 : ℚ) ≤
      ((centerRowsBelow 587).map (fun r ↦ r.lo * Analysis.gammaFiniteEulerLower r.ratios)).sum := by
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using
    centerRowsBelow_euler_lower (by norm_num only : 587 ≤ 50000) (20373 / 5000) hc

/-- Under RH, the fixed-scale principal, Euler and main bounds give a strict
Gamma gap up to the certified endpoint for cutoff 587. -/
theorem gammaFixed17Cell18_gap (hRH : RiemannHypothesis) {L : ℝ}
    (hL : L ≤ (gammaFixed17Cell18Right : ℝ)) :
    (∑' k : ℕ,
              Real.exp (-(k : ℝ) / (gammaMainCell17Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
                Real.sqrt (gammaMainCell17Scale : ℝ)) +
            2 * (11783423 / 25000000 : ℝ) * L -
          477 / 100 +
        ((∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
          4 * ∑ k ∈ Finset.Ioc (0 : ℕ) 587, Analysis.gammaResolventMangoldtWeight k) +
        ((7 / 3 : ℝ) * L + 12) / Real.sqrt (gammaMainCell17Scale : ℝ) +
        (105 / 2 : ℝ) * (gammaMainCell17Scale : ℝ) ^ (-9 / 16 : ℝ) +
        3 / ((gammaMainCell17Scale : ℝ) * Real.sqrt (gammaMainCell17Scale : ℝ)) <
      4 *
        ∑ k ∈ Finset.Ioc (0 : ℕ) 587,
          Real.exp (-(k : ℝ) / (gammaMainCell17Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
            Real.sqrt (gammaMainCell17Scale : ℝ) := by
  apply
    gamma_gap_of_cell_caps (Finset.Ioc 0 587) (gammaMainCell17Scale : ℝ) L
      (gammaFixed17Cell18Right : ℝ) (1918 / 100) (3603 / 100000) (gammaFixed17Main18Lower : ℝ)
      (19101321 / 1000000) (20373 / 5000)
      (by norm_num only [gammaMainCell17Scale, Rat.cast_div, Rat.cast_ofNat]) (by norm_num only)
      (by norm_num only [gammaMainCell17Scale, Rat.cast_div, Rat.cast_ofNat])
      (by norm_num only [gammaFixed17Cell18Right, Rat.cast_div, Rat.cast_ofNat]) hL
      gammaCell17_power_upper gammaFixed17Main18_actual_lower
      (by
        simpa only [gammaUpperCell17Scale, gammaMainCell17Scale] using gammaCell17_principal_upper)
      gammaFixed17Cell18_euler_lower (euler_mass_le_12372 hRH)
  norm_num only [gammaFixed17Cell18Right, gammaMainCell17Scale, gammaFixed17Main18Lower,
    Rat.cast_div, Rat.cast_ofNat]

/-- The right endpoint reached by the fixed-scale cutoff 601. -/
def gammaFixed17Cell21Right : ℚ :=
  11355982270739 / 250000000000

/-- The Euler prefix through 601 exceeds the rational lower cap.
The center-row certificate gives the finite sum comparison. -/
theorem gammaFixed17Cell21_euler_lower :
    (10223 / 2500 : ℝ) ≤ ∑ n ∈ Finset.Ioc (0 : ℕ) 601, Analysis.gammaResolventMangoldtWeight n := by
  have hc :
    (10223 / 2500 : ℚ) ≤
      ((centerRowsBelow 601).map (fun r ↦ r.lo * Analysis.gammaFiniteEulerLower r.ratios)).sum := by
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using
    centerRowsBelow_euler_lower (by norm_num only : 601 ≤ 50000) (10223 / 2500) hc

/-- Under RH, the fixed-scale principal, Euler and main bounds give a strict
Gamma gap up to the certified endpoint for cutoff 601. -/
theorem gammaFixed17Cell21_gap (hRH : RiemannHypothesis) {L : ℝ}
    (hL : L ≤ (gammaFixed17Cell21Right : ℝ)) :
    (∑' k : ℕ,
              Real.exp (-(k : ℝ) / (gammaMainCell17Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
                Real.sqrt (gammaMainCell17Scale : ℝ)) +
            2 * (11783423 / 25000000 : ℝ) * L -
          477 / 100 +
        ((∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
          4 * ∑ k ∈ Finset.Ioc (0 : ℕ) 601, Analysis.gammaResolventMangoldtWeight k) +
        ((7 / 3 : ℝ) * L + 12) / Real.sqrt (gammaMainCell17Scale : ℝ) +
        (105 / 2 : ℝ) * (gammaMainCell17Scale : ℝ) ^ (-9 / 16 : ℝ) +
        3 / ((gammaMainCell17Scale : ℝ) * Real.sqrt (gammaMainCell17Scale : ℝ)) <
      4 *
        ∑ k ∈ Finset.Ioc (0 : ℕ) 601,
          Real.exp (-(k : ℝ) / (gammaMainCell17Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
            Real.sqrt (gammaMainCell17Scale : ℝ) := by
  apply
    gamma_gap_of_cell_caps (Finset.Ioc 0 601) (gammaMainCell17Scale : ℝ) L
      (gammaFixed17Cell21Right : ℝ) (1918 / 100) (3603 / 100000) (gammaFixed17Main21Lower : ℝ)
      (19101321 / 1000000) (10223 / 2500)
      (by norm_num only [gammaMainCell17Scale, Rat.cast_div, Rat.cast_ofNat]) (by norm_num only)
      (by norm_num only [gammaMainCell17Scale, Rat.cast_div, Rat.cast_ofNat])
      (by norm_num only [gammaFixed17Cell21Right, Rat.cast_div, Rat.cast_ofNat]) hL
      gammaCell17_power_upper gammaFixed17Main21_actual_lower
      (by
        simpa only [gammaUpperCell17Scale, gammaMainCell17Scale] using gammaCell17_principal_upper)
      gammaFixed17Cell21_euler_lower (euler_mass_le_12372 hRH)
  norm_num only [gammaFixed17Cell21Right, gammaMainCell17Scale, gammaFixed17Main21Lower,
    Rat.cast_div, Rat.cast_ofNat]

/-- The right endpoint reached by the fixed-scale cutoff 619. -/
def gammaFixed17Cell25Right : ℚ :=
  46439925351649 / 1000000000000

/-- The Euler prefix through 619 exceeds the rational lower cap.
The center-row certificate gives the finite sum comparison. -/
theorem gammaFixed17Cell25_euler_lower :
    (41081 / 10000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 619, Analysis.gammaResolventMangoldtWeight n := by
  have hc :
    (41081 / 10000 : ℚ) ≤
      ((centerRowsBelow 619).map (fun r ↦ r.lo * Analysis.gammaFiniteEulerLower r.ratios)).sum := by
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using
    centerRowsBelow_euler_lower (by norm_num only : 619 ≤ 50000) (41081 / 10000) hc

/-- Under RH, the fixed-scale principal, Euler and main bounds give a strict
Gamma gap up to the certified endpoint for cutoff 619. -/
theorem gammaFixed17Cell25_gap (hRH : RiemannHypothesis) {L : ℝ}
    (hL : L ≤ (gammaFixed17Cell25Right : ℝ)) :
    (∑' k : ℕ,
              Real.exp (-(k : ℝ) / (gammaMainCell17Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
                Real.sqrt (gammaMainCell17Scale : ℝ)) +
            2 * (11783423 / 25000000 : ℝ) * L -
          477 / 100 +
        ((∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
          4 * ∑ k ∈ Finset.Ioc (0 : ℕ) 619, Analysis.gammaResolventMangoldtWeight k) +
        ((7 / 3 : ℝ) * L + 12) / Real.sqrt (gammaMainCell17Scale : ℝ) +
        (105 / 2 : ℝ) * (gammaMainCell17Scale : ℝ) ^ (-9 / 16 : ℝ) +
        3 / ((gammaMainCell17Scale : ℝ) * Real.sqrt (gammaMainCell17Scale : ℝ)) <
      4 *
        ∑ k ∈ Finset.Ioc (0 : ℕ) 619,
          Real.exp (-(k : ℝ) / (gammaMainCell17Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
            Real.sqrt (gammaMainCell17Scale : ℝ) := by
  apply
    gamma_gap_of_cell_caps (Finset.Ioc 0 619) (gammaMainCell17Scale : ℝ) L
      (gammaFixed17Cell25Right : ℝ) (1918 / 100) (3603 / 100000) (gammaFixed17Main25Lower : ℝ)
      (19101321 / 1000000) (41081 / 10000)
      (by norm_num only [gammaMainCell17Scale, Rat.cast_div, Rat.cast_ofNat]) (by norm_num only)
      (by norm_num only [gammaMainCell17Scale, Rat.cast_div, Rat.cast_ofNat])
      (by norm_num only [gammaFixed17Cell25Right, Rat.cast_div, Rat.cast_ofNat]) hL
      gammaCell17_power_upper gammaFixed17Main25_actual_lower
      (by
        simpa only [gammaUpperCell17Scale, gammaMainCell17Scale] using gammaCell17_principal_upper)
      gammaFixed17Cell25_euler_lower (euler_mass_le_12372 hRH)
  norm_num only [gammaFixed17Cell25Right, gammaMainCell17Scale, gammaFixed17Main25Lower,
    Rat.cast_div, Rat.cast_ofNat]

/-- The right endpoint reached by the fixed-scale cutoff 647. -/
def gammaFixed17Cell30Right : ℚ :=
  1187609644061 / 25000000000

/-- The Euler prefix through 647 exceeds the rational lower cap.
The center-row certificate gives the finite sum comparison. -/
theorem gammaFixed17Cell30_euler_lower :
    (10319 / 2500 : ℝ) ≤ ∑ n ∈ Finset.Ioc (0 : ℕ) 647, Analysis.gammaResolventMangoldtWeight n := by
  have hc :
    (10319 / 2500 : ℚ) ≤
      ((centerRowsBelow 647).map (fun r ↦ r.lo * Analysis.gammaFiniteEulerLower r.ratios)).sum := by
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using
    centerRowsBelow_euler_lower (by norm_num only : 647 ≤ 50000) (10319 / 2500) hc

/-- Under RH, the fixed-scale principal, Euler and main bounds give a strict
Gamma gap up to the certified endpoint for cutoff 647. -/
theorem gammaFixed17Cell30_gap (hRH : RiemannHypothesis) {L : ℝ}
    (hL : L ≤ (gammaFixed17Cell30Right : ℝ)) :
    (∑' k : ℕ,
              Real.exp (-(k : ℝ) / (gammaMainCell17Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
                Real.sqrt (gammaMainCell17Scale : ℝ)) +
            2 * (11783423 / 25000000 : ℝ) * L -
          477 / 100 +
        ((∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
          4 * ∑ k ∈ Finset.Ioc (0 : ℕ) 647, Analysis.gammaResolventMangoldtWeight k) +
        ((7 / 3 : ℝ) * L + 12) / Real.sqrt (gammaMainCell17Scale : ℝ) +
        (105 / 2 : ℝ) * (gammaMainCell17Scale : ℝ) ^ (-9 / 16 : ℝ) +
        3 / ((gammaMainCell17Scale : ℝ) * Real.sqrt (gammaMainCell17Scale : ℝ)) <
      4 *
        ∑ k ∈ Finset.Ioc (0 : ℕ) 647,
          Real.exp (-(k : ℝ) / (gammaMainCell17Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
            Real.sqrt (gammaMainCell17Scale : ℝ) := by
  apply
    gamma_gap_of_cell_caps (Finset.Ioc 0 647) (gammaMainCell17Scale : ℝ) L
      (gammaFixed17Cell30Right : ℝ) (1918 / 100) (3603 / 100000) (gammaFixed17Main30Lower : ℝ)
      (19101321 / 1000000) (10319 / 2500)
      (by norm_num only [gammaMainCell17Scale, Rat.cast_div, Rat.cast_ofNat]) (by norm_num only)
      (by norm_num only [gammaMainCell17Scale, Rat.cast_div, Rat.cast_ofNat])
      (by norm_num only [gammaFixed17Cell30Right, Rat.cast_div, Rat.cast_ofNat]) hL
      gammaCell17_power_upper gammaFixed17Main30_actual_lower
      (by
        simpa only [gammaUpperCell17Scale, gammaMainCell17Scale] using gammaCell17_principal_upper)
      gammaFixed17Cell30_euler_lower (euler_mass_le_12372 hRH)
  norm_num only [gammaFixed17Cell30Right, gammaMainCell17Scale, gammaFixed17Main30Lower,
    Rat.cast_div, Rat.cast_ofNat]

/-- The right endpoint reached by the fixed-scale cutoff 677. -/
def gammaFixed17Cell35Right : ℚ :=
  2430706344529 / 50000000000

/-- The Euler prefix through 677 exceeds the rational lower cap.
The center-row certificate gives the finite sum comparison. -/
theorem gammaFixed17Cell35_euler_lower :
    (5187 / 1250 : ℝ) ≤ ∑ n ∈ Finset.Ioc (0 : ℕ) 677, Analysis.gammaResolventMangoldtWeight n := by
  have hc :
    (5187 / 1250 : ℚ) ≤
      ((centerRowsBelow 677).map (fun r ↦ r.lo * Analysis.gammaFiniteEulerLower r.ratios)).sum := by
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using
    centerRowsBelow_euler_lower (by norm_num only : 677 ≤ 50000) (5187 / 1250) hc

/-- Under RH, the fixed-scale principal, Euler and main bounds give a strict
Gamma gap up to the certified endpoint for cutoff 677. -/
theorem gammaFixed17Cell35_gap (hRH : RiemannHypothesis) {L : ℝ}
    (hL : L ≤ (gammaFixed17Cell35Right : ℝ)) :
    (∑' k : ℕ,
              Real.exp (-(k : ℝ) / (gammaMainCell17Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
                Real.sqrt (gammaMainCell17Scale : ℝ)) +
            2 * (11783423 / 25000000 : ℝ) * L -
          477 / 100 +
        ((∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
          4 * ∑ k ∈ Finset.Ioc (0 : ℕ) 677, Analysis.gammaResolventMangoldtWeight k) +
        ((7 / 3 : ℝ) * L + 12) / Real.sqrt (gammaMainCell17Scale : ℝ) +
        (105 / 2 : ℝ) * (gammaMainCell17Scale : ℝ) ^ (-9 / 16 : ℝ) +
        3 / ((gammaMainCell17Scale : ℝ) * Real.sqrt (gammaMainCell17Scale : ℝ)) <
      4 *
        ∑ k ∈ Finset.Ioc (0 : ℕ) 677,
          Real.exp (-(k : ℝ) / (gammaMainCell17Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
            Real.sqrt (gammaMainCell17Scale : ℝ) := by
  apply
    gamma_gap_of_cell_caps (Finset.Ioc 0 677) (gammaMainCell17Scale : ℝ) L
      (gammaFixed17Cell35Right : ℝ) (1918 / 100) (3603 / 100000) (gammaFixed17Main35Lower : ℝ)
      (19101321 / 1000000) (5187 / 1250)
      (by norm_num only [gammaMainCell17Scale, Rat.cast_div, Rat.cast_ofNat]) (by norm_num only)
      (by norm_num only [gammaMainCell17Scale, Rat.cast_div, Rat.cast_ofNat])
      (by norm_num only [gammaFixed17Cell35Right, Rat.cast_div, Rat.cast_ofNat]) hL
      gammaCell17_power_upper gammaFixed17Main35_actual_lower
      (by
        simpa only [gammaUpperCell17Scale, gammaMainCell17Scale] using gammaCell17_principal_upper)
      gammaFixed17Cell35_euler_lower (euler_mass_le_12372 hRH)
  norm_num only [gammaFixed17Cell35Right, gammaMainCell17Scale, gammaFixed17Main35Lower,
    Rat.cast_div, Rat.cast_ofNat]

end PseudoPrime.PrimeTestBounds.MillerRabin
