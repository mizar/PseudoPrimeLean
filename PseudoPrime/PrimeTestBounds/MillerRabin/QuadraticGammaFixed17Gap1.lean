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

/-- The right endpoint reached by the fixed-scale cutoff 709. -/
def gammaFixed17Cell39Right : ℚ :=
  49430085305747 / 1000000000000

/-- The Euler prefix through 709 exceeds the rational lower cap.
The center-row certificate gives the finite sum comparison. -/
theorem gammaFixed17Cell39_euler_lower :
    (8333 / 2000 : ℝ) ≤ ∑ n ∈ Finset.Ioc (0 : ℕ) 709, Analysis.gammaResolventMangoldtWeight n := by
  have hc :
    (8333 / 2000 : ℚ) ≤
      ((centerRowsBelow 709).map (fun r ↦ r.lo * Analysis.gammaFiniteEulerLower r.ratios)).sum := by
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using
    centerRowsBelow_euler_lower (by norm_num only : 709 ≤ 50000) (8333 / 2000) hc

/-- Under RH, the fixed-scale principal, Euler and main bounds give a strict
Gamma gap up to the certified endpoint for cutoff 709. -/
theorem gammaFixed17Cell39_gap (hRH : RiemannHypothesis) {L : ℝ}
    (hL : L ≤ (gammaFixed17Cell39Right : ℝ)) :
    (∑' k : ℕ,
              Real.exp (-(k : ℝ) / (gammaMainCell17Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
                Real.sqrt (gammaMainCell17Scale : ℝ)) +
            2 * (11783423 / 25000000 : ℝ) * L -
          477 / 100 +
        ((∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
          4 * ∑ k ∈ Finset.Ioc (0 : ℕ) 709, Analysis.gammaResolventMangoldtWeight k) +
        ((7 / 3 : ℝ) * L + 12) / Real.sqrt (gammaMainCell17Scale : ℝ) +
        (105 / 2 : ℝ) * (gammaMainCell17Scale : ℝ) ^ (-9 / 16 : ℝ) +
        3 / ((gammaMainCell17Scale : ℝ) * Real.sqrt (gammaMainCell17Scale : ℝ)) <
      4 *
        ∑ k ∈ Finset.Ioc (0 : ℕ) 709,
          Real.exp (-(k : ℝ) / (gammaMainCell17Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
            Real.sqrt (gammaMainCell17Scale : ℝ) := by
  apply
    gamma_gap_of_cell_caps (Finset.Ioc 0 709) (gammaMainCell17Scale : ℝ) L
      (gammaFixed17Cell39Right : ℝ) (1918 / 100) (3603 / 100000) (gammaFixed17Main39Lower : ℝ)
      (19101321 / 1000000) (8333 / 2000)
      (by norm_num only [gammaMainCell17Scale, Rat.cast_div, Rat.cast_ofNat]) (by norm_num only)
      (by norm_num only [gammaMainCell17Scale, Rat.cast_div, Rat.cast_ofNat])
      (by norm_num only [gammaFixed17Cell39Right, Rat.cast_div, Rat.cast_ofNat]) hL
      gammaCell17_power_upper gammaFixed17Main39_actual_lower
      (by
        simpa only [gammaUpperCell17Scale, gammaMainCell17Scale] using gammaCell17_principal_upper)
      gammaFixed17Cell39_euler_lower (euler_mass_le_12372 hRH)
  norm_num only [gammaFixed17Cell39Right, gammaMainCell17Scale, gammaFixed17Main39Lower,
    Rat.cast_div, Rat.cast_ofNat]

/-- The right endpoint reached by the fixed-scale cutoff 733. -/
def gammaFixed17Cell43Right : ℚ :=
  6254165278703 / 125000000000

/-- The Euler prefix through 733 exceeds the rational lower cap.
The center-row certificate gives the finite sum comparison. -/
theorem gammaFixed17Cell43_euler_lower :
    (41793 / 10000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 733, Analysis.gammaResolventMangoldtWeight n := by
  have hc :
    (41793 / 10000 : ℚ) ≤
      ((centerRowsBelow 733).map (fun r ↦ r.lo * Analysis.gammaFiniteEulerLower r.ratios)).sum := by
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using
    centerRowsBelow_euler_lower (by norm_num only : 733 ≤ 50000) (41793 / 10000) hc

/-- Under RH, the fixed-scale principal, Euler and main bounds give a strict
Gamma gap up to the certified endpoint for cutoff 733. -/
theorem gammaFixed17Cell43_gap (hRH : RiemannHypothesis) {L : ℝ}
    (hL : L ≤ (gammaFixed17Cell43Right : ℝ)) :
    (∑' k : ℕ,
              Real.exp (-(k : ℝ) / (gammaMainCell17Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
                Real.sqrt (gammaMainCell17Scale : ℝ)) +
            2 * (11783423 / 25000000 : ℝ) * L -
          477 / 100 +
        ((∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
          4 * ∑ k ∈ Finset.Ioc (0 : ℕ) 733, Analysis.gammaResolventMangoldtWeight k) +
        ((7 / 3 : ℝ) * L + 12) / Real.sqrt (gammaMainCell17Scale : ℝ) +
        (105 / 2 : ℝ) * (gammaMainCell17Scale : ℝ) ^ (-9 / 16 : ℝ) +
        3 / ((gammaMainCell17Scale : ℝ) * Real.sqrt (gammaMainCell17Scale : ℝ)) <
      4 *
        ∑ k ∈ Finset.Ioc (0 : ℕ) 733,
          Real.exp (-(k : ℝ) / (gammaMainCell17Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
            Real.sqrt (gammaMainCell17Scale : ℝ) := by
  apply
    gamma_gap_of_cell_caps (Finset.Ioc 0 733) (gammaMainCell17Scale : ℝ) L
      (gammaFixed17Cell43Right : ℝ) (1918 / 100) (3603 / 100000) (gammaFixed17Main43Lower : ℝ)
      (19101321 / 1000000) (41793 / 10000)
      (by norm_num only [gammaMainCell17Scale, Rat.cast_div, Rat.cast_ofNat]) (by norm_num only)
      (by norm_num only [gammaMainCell17Scale, Rat.cast_div, Rat.cast_ofNat])
      (by norm_num only [gammaFixed17Cell43Right, Rat.cast_div, Rat.cast_ofNat]) hL
      gammaCell17_power_upper gammaFixed17Main43_actual_lower
      (by
        simpa only [gammaUpperCell17Scale, gammaMainCell17Scale] using gammaCell17_principal_upper)
      gammaFixed17Cell43_euler_lower (euler_mass_le_12372 hRH)
  norm_num only [gammaFixed17Cell43Right, gammaMainCell17Scale, gammaFixed17Main43Lower,
    Rat.cast_div, Rat.cast_ofNat]

/-- The right endpoint reached by the fixed-scale cutoff 751. -/
def gammaFixed17Cell46Right : ℚ :=
  50629372239179 / 1000000000000

/-- The Euler prefix through 751 exceeds the rational lower cap.
The center-row certificate gives the finite sum comparison. -/
theorem gammaFixed17Cell46_euler_lower :
    (5239 / 1250 : ℝ) ≤ ∑ n ∈ Finset.Ioc (0 : ℕ) 751, Analysis.gammaResolventMangoldtWeight n := by
  have hc :
    (5239 / 1250 : ℚ) ≤
      ((centerRowsBelow 751).map (fun r ↦ r.lo * Analysis.gammaFiniteEulerLower r.ratios)).sum := by
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using
    centerRowsBelow_euler_lower (by norm_num only : 751 ≤ 50000) (5239 / 1250) hc

/-- Under RH, the fixed-scale principal, Euler and main bounds give a strict
Gamma gap up to the certified endpoint for cutoff 751. -/
theorem gammaFixed17Cell46_gap (hRH : RiemannHypothesis) {L : ℝ}
    (hL : L ≤ (gammaFixed17Cell46Right : ℝ)) :
    (∑' k : ℕ,
              Real.exp (-(k : ℝ) / (gammaMainCell17Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
                Real.sqrt (gammaMainCell17Scale : ℝ)) +
            2 * (11783423 / 25000000 : ℝ) * L -
          477 / 100 +
        ((∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
          4 * ∑ k ∈ Finset.Ioc (0 : ℕ) 751, Analysis.gammaResolventMangoldtWeight k) +
        ((7 / 3 : ℝ) * L + 12) / Real.sqrt (gammaMainCell17Scale : ℝ) +
        (105 / 2 : ℝ) * (gammaMainCell17Scale : ℝ) ^ (-9 / 16 : ℝ) +
        3 / ((gammaMainCell17Scale : ℝ) * Real.sqrt (gammaMainCell17Scale : ℝ)) <
      4 *
        ∑ k ∈ Finset.Ioc (0 : ℕ) 751,
          Real.exp (-(k : ℝ) / (gammaMainCell17Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
            Real.sqrt (gammaMainCell17Scale : ℝ) := by
  apply
    gamma_gap_of_cell_caps (Finset.Ioc 0 751) (gammaMainCell17Scale : ℝ) L
      (gammaFixed17Cell46Right : ℝ) (1918 / 100) (3603 / 100000) (gammaFixed17Main46Lower : ℝ)
      (19101321 / 1000000) (5239 / 1250)
      (by norm_num only [gammaMainCell17Scale, Rat.cast_div, Rat.cast_ofNat]) (by norm_num only)
      (by norm_num only [gammaMainCell17Scale, Rat.cast_div, Rat.cast_ofNat])
      (by norm_num only [gammaFixed17Cell46Right, Rat.cast_div, Rat.cast_ofNat]) hL
      gammaCell17_power_upper gammaFixed17Main46_actual_lower
      (by
        simpa only [gammaUpperCell17Scale, gammaMainCell17Scale] using gammaCell17_principal_upper)
      gammaFixed17Cell46_euler_lower (euler_mass_le_12372 hRH)
  norm_num only [gammaFixed17Cell46Right, gammaMainCell17Scale, gammaFixed17Main46Lower,
    Rat.cast_div, Rat.cast_ofNat]

/-- The right endpoint reached by the fixed-scale cutoff 769. -/
def gammaFixed17Cell49Right : ℚ :=
  51218486246017 / 1000000000000

/-- The Euler prefix through 769 exceeds the rational lower cap.
The center-row certificate gives the finite sum comparison. -/
theorem gammaFixed17Cell49_euler_lower :
    (42029 / 10000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 769, Analysis.gammaResolventMangoldtWeight n := by
  have hc :
    (42029 / 10000 : ℚ) ≤
      ((centerRowsBelow 769).map (fun r ↦ r.lo * Analysis.gammaFiniteEulerLower r.ratios)).sum := by
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using
    centerRowsBelow_euler_lower (by norm_num only : 769 ≤ 50000) (42029 / 10000) hc

/-- Under RH, the fixed-scale principal, Euler and main bounds give a strict
Gamma gap up to the certified endpoint for cutoff 769. -/
theorem gammaFixed17Cell49_gap (hRH : RiemannHypothesis) {L : ℝ}
    (hL : L ≤ (gammaFixed17Cell49Right : ℝ)) :
    (∑' k : ℕ,
              Real.exp (-(k : ℝ) / (gammaMainCell17Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
                Real.sqrt (gammaMainCell17Scale : ℝ)) +
            2 * (11783423 / 25000000 : ℝ) * L -
          477 / 100 +
        ((∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
          4 * ∑ k ∈ Finset.Ioc (0 : ℕ) 769, Analysis.gammaResolventMangoldtWeight k) +
        ((7 / 3 : ℝ) * L + 12) / Real.sqrt (gammaMainCell17Scale : ℝ) +
        (105 / 2 : ℝ) * (gammaMainCell17Scale : ℝ) ^ (-9 / 16 : ℝ) +
        3 / ((gammaMainCell17Scale : ℝ) * Real.sqrt (gammaMainCell17Scale : ℝ)) <
      4 *
        ∑ k ∈ Finset.Ioc (0 : ℕ) 769,
          Real.exp (-(k : ℝ) / (gammaMainCell17Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
            Real.sqrt (gammaMainCell17Scale : ℝ) := by
  apply
    gamma_gap_of_cell_caps (Finset.Ioc 0 769) (gammaMainCell17Scale : ℝ) L
      (gammaFixed17Cell49Right : ℝ) (1918 / 100) (3603 / 100000) (gammaFixed17Main49Lower : ℝ)
      (19101321 / 1000000) (42029 / 10000)
      (by norm_num only [gammaMainCell17Scale, Rat.cast_div, Rat.cast_ofNat]) (by norm_num only)
      (by norm_num only [gammaMainCell17Scale, Rat.cast_div, Rat.cast_ofNat])
      (by norm_num only [gammaFixed17Cell49Right, Rat.cast_div, Rat.cast_ofNat]) hL
      gammaCell17_power_upper gammaFixed17Main49_actual_lower
      (by
        simpa only [gammaUpperCell17Scale, gammaMainCell17Scale] using gammaCell17_principal_upper)
      gammaFixed17Cell49_euler_lower (euler_mass_le_12372 hRH)
  norm_num only [gammaFixed17Cell49Right, gammaMainCell17Scale, gammaFixed17Main49Lower,
    Rat.cast_div, Rat.cast_ofNat]

/-- The right endpoint reached by the fixed-scale cutoff 787. -/
def gammaFixed17Cell51Right : ℚ :=
  51542862422131 / 1000000000000

/-- The Euler prefix through 787 exceeds the rational lower cap.
The center-row certificate gives the finite sum comparison. -/
theorem gammaFixed17Cell51_euler_lower :
    (8421 / 2000 : ℝ) ≤ ∑ n ∈ Finset.Ioc (0 : ℕ) 787, Analysis.gammaResolventMangoldtWeight n := by
  have hc :
    (8421 / 2000 : ℚ) ≤
      ((centerRowsBelow 787).map (fun r ↦ r.lo * Analysis.gammaFiniteEulerLower r.ratios)).sum := by
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using
    centerRowsBelow_euler_lower (by norm_num only : 787 ≤ 50000) (8421 / 2000) hc

/-- Under RH, the fixed-scale principal, Euler and main bounds give a strict
Gamma gap up to the certified endpoint for cutoff 787. -/
theorem gammaFixed17Cell51_gap (hRH : RiemannHypothesis) {L : ℝ}
    (hL : L ≤ (gammaFixed17Cell51Right : ℝ)) :
    (∑' k : ℕ,
              Real.exp (-(k : ℝ) / (gammaMainCell17Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
                Real.sqrt (gammaMainCell17Scale : ℝ)) +
            2 * (11783423 / 25000000 : ℝ) * L -
          477 / 100 +
        ((∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
          4 * ∑ k ∈ Finset.Ioc (0 : ℕ) 787, Analysis.gammaResolventMangoldtWeight k) +
        ((7 / 3 : ℝ) * L + 12) / Real.sqrt (gammaMainCell17Scale : ℝ) +
        (105 / 2 : ℝ) * (gammaMainCell17Scale : ℝ) ^ (-9 / 16 : ℝ) +
        3 / ((gammaMainCell17Scale : ℝ) * Real.sqrt (gammaMainCell17Scale : ℝ)) <
      4 *
        ∑ k ∈ Finset.Ioc (0 : ℕ) 787,
          Real.exp (-(k : ℝ) / (gammaMainCell17Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
            Real.sqrt (gammaMainCell17Scale : ℝ) := by
  apply
    gamma_gap_of_cell_caps (Finset.Ioc 0 787) (gammaMainCell17Scale : ℝ) L
      (gammaFixed17Cell51Right : ℝ) (1918 / 100) (3603 / 100000) (gammaFixed17Main51Lower : ℝ)
      (19101321 / 1000000) (8421 / 2000)
      (by norm_num only [gammaMainCell17Scale, Rat.cast_div, Rat.cast_ofNat]) (by norm_num only)
      (by norm_num only [gammaMainCell17Scale, Rat.cast_div, Rat.cast_ofNat])
      (by norm_num only [gammaFixed17Cell51Right, Rat.cast_div, Rat.cast_ofNat]) hL
      gammaCell17_power_upper gammaFixed17Main51_actual_lower
      (by
        simpa only [gammaUpperCell17Scale, gammaMainCell17Scale] using gammaCell17_principal_upper)
      gammaFixed17Cell51_euler_lower (euler_mass_le_12372 hRH)
  norm_num only [gammaFixed17Cell51Right, gammaMainCell17Scale, gammaFixed17Main51Lower,
    Rat.cast_div, Rat.cast_ofNat]

end PseudoPrime.PrimeTestBounds.MillerRabin
