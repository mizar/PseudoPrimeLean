/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaFixed260Main1
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaFixed260Principal

/-! # Fixed-scale Gamma gaps across multiple cells -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The right endpoint reached by the fixed-scale cutoff 2099. -/
def gammaFixed260Cell238Right : ℚ :=
  87768635248211 / 1000000000000

/-- The Euler prefix through 2099 exceeds the rational lower cap.
The center-row certificate gives the finite sum comparison. -/
theorem gammaFixed260Cell238_euler_lower :
    (463 / 100 : ℝ) ≤ ∑ n ∈ Finset.Ioc (0 : ℕ) 2099, Analysis.gammaResolventMangoldtWeight n := by
  have hc :
    (463 / 100 : ℚ) ≤
      ((centerRowsBelow 2099).map
          (fun r ↦ r.lo * Analysis.gammaFiniteEulerLower r.ratios)).sum := by
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using
    centerRowsBelow_euler_lower (by norm_num only : 2099 ≤ 50000) (463 / 100) hc

/-- Under RH, the fixed-scale principal, Euler and main bounds give a strict
Gamma gap up to the certified endpoint for cutoff 2099. -/
theorem gammaFixed260Cell238_gap (hRH : RiemannHypothesis) {L : ℝ}
    (hL : L ≤ (gammaFixed260Cell238Right : ℝ)) :
    (∑' k : ℕ,
              Real.exp (-(k : ℝ) / (gammaMainCell260Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
                Real.sqrt (gammaMainCell260Scale : ℝ)) +
            2 * (11783423 / 25000000 : ℝ) * L -
          477 / 100 +
        ((∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
          4 * ∑ k ∈ Finset.Ioc (0 : ℕ) 2099, Analysis.gammaResolventMangoldtWeight k) +
        ((7 / 3 : ℝ) * L + 12) / Real.sqrt (gammaMainCell260Scale : ℝ) +
        (105 / 2 : ℝ) * (gammaMainCell260Scale : ℝ) ^ (-9 / 16 : ℝ) +
        3 / ((gammaMainCell260Scale : ℝ) * Real.sqrt (gammaMainCell260Scale : ℝ)) <
      4 *
        ∑ k ∈ Finset.Ioc (0 : ℕ) 2099,
          Real.exp (-(k : ℝ) / (gammaMainCell260Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
            Real.sqrt (gammaMainCell260Scale : ℝ) := by
  apply
    gamma_gap_of_cell_caps (Finset.Ioc 0 2099) (gammaMainCell260Scale : ℝ) L
      (gammaFixed260Cell238Right : ℝ) (3645 / 100) (1751 / 100000) (gammaFixed260Main238Lower : ℝ)
      (3687 / 100) (463 / 100)
      (by norm_num only [gammaMainCell260Scale, Rat.cast_div, Rat.cast_ofNat]) (by norm_num only)
      (by norm_num only [gammaMainCell260Scale, Rat.cast_div, Rat.cast_ofNat])
      (by norm_num only [gammaFixed260Cell238Right, Rat.cast_div, Rat.cast_ofNat]) hL
      gammaFixed260_power_upper gammaFixed260Main238_actual_lower
      (gammaFixed260_principal_upper hRH) gammaFixed260Cell238_euler_lower (euler_mass_le_12372 hRH)
  norm_num only [gammaFixed260Cell238Right, gammaMainCell260Scale, gammaFixed260Main238Lower,
    Rat.cast_div, Rat.cast_ofNat]

/-- The right endpoint reached by the fixed-scale cutoff 2311. -/
def gammaFixed260Cell268Right : ℚ :=
  92321900615907 / 1000000000000

/-- The Euler prefix through 2311 exceeds the rational lower cap.
The center-row certificate gives the finite sum comparison. -/
theorem gammaFixed260Cell268_euler_lower :
    (46699 / 10000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 2311, Analysis.gammaResolventMangoldtWeight n := by
  have hc :
    (46699 / 10000 : ℚ) ≤
      ((centerRowsBelow 2311).map
          (fun r ↦ r.lo * Analysis.gammaFiniteEulerLower r.ratios)).sum := by
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using
    centerRowsBelow_euler_lower (by norm_num only : 2311 ≤ 50000) (46699 / 10000) hc

/-- Under RH, the fixed-scale principal, Euler and main bounds give a strict
Gamma gap up to the certified endpoint for cutoff 2311. -/
theorem gammaFixed260Cell268_gap (hRH : RiemannHypothesis) {L : ℝ}
    (hL : L ≤ (gammaFixed260Cell268Right : ℝ)) :
    (∑' k : ℕ,
              Real.exp (-(k : ℝ) / (gammaMainCell260Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
                Real.sqrt (gammaMainCell260Scale : ℝ)) +
            2 * (11783423 / 25000000 : ℝ) * L -
          477 / 100 +
        ((∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
          4 * ∑ k ∈ Finset.Ioc (0 : ℕ) 2311, Analysis.gammaResolventMangoldtWeight k) +
        ((7 / 3 : ℝ) * L + 12) / Real.sqrt (gammaMainCell260Scale : ℝ) +
        (105 / 2 : ℝ) * (gammaMainCell260Scale : ℝ) ^ (-9 / 16 : ℝ) +
        3 / ((gammaMainCell260Scale : ℝ) * Real.sqrt (gammaMainCell260Scale : ℝ)) <
      4 *
        ∑ k ∈ Finset.Ioc (0 : ℕ) 2311,
          Real.exp (-(k : ℝ) / (gammaMainCell260Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
            Real.sqrt (gammaMainCell260Scale : ℝ) := by
  apply
    gamma_gap_of_cell_caps (Finset.Ioc 0 2311) (gammaMainCell260Scale : ℝ) L
      (gammaFixed260Cell268Right : ℝ) (3645 / 100) (1751 / 100000) (gammaFixed260Main268Lower : ℝ)
      (3687 / 100) (46699 / 10000)
      (by norm_num only [gammaMainCell260Scale, Rat.cast_div, Rat.cast_ofNat]) (by norm_num only)
      (by norm_num only [gammaMainCell260Scale, Rat.cast_div, Rat.cast_ofNat])
      (by norm_num only [gammaFixed260Cell268Right, Rat.cast_div, Rat.cast_ofNat]) hL
      gammaFixed260_power_upper gammaFixed260Main268_actual_lower
      (gammaFixed260_principal_upper hRH) gammaFixed260Cell268_euler_lower (euler_mass_le_12372 hRH)
  norm_num only [gammaFixed260Cell268Right, gammaMainCell260Scale, gammaFixed260Main268Lower,
    Rat.cast_div, Rat.cast_ofNat]

/-- The right endpoint reached by the fixed-scale cutoff 2557. -/
def gammaFixed260Cell300Right : ℚ :=
  4838215924629 / 50000000000

/-- The Euler prefix through 2557 exceeds the rational lower cap.
The center-row certificate gives the finite sum comparison. -/
theorem gammaFixed260Cell300_euler_lower :
    (47107 / 10000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 2557, Analysis.gammaResolventMangoldtWeight n := by
  have hc :
    (47107 / 10000 : ℚ) ≤
      ((centerRowsBelow 2557).map
          (fun r ↦ r.lo * Analysis.gammaFiniteEulerLower r.ratios)).sum := by
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using
    centerRowsBelow_euler_lower (by norm_num only : 2557 ≤ 50000) (47107 / 10000) hc

/-- Under RH, the fixed-scale principal, Euler and main bounds give a strict
Gamma gap up to the certified endpoint for cutoff 2557. -/
theorem gammaFixed260Cell300_gap (hRH : RiemannHypothesis) {L : ℝ}
    (hL : L ≤ (gammaFixed260Cell300Right : ℝ)) :
    (∑' k : ℕ,
              Real.exp (-(k : ℝ) / (gammaMainCell260Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
                Real.sqrt (gammaMainCell260Scale : ℝ)) +
            2 * (11783423 / 25000000 : ℝ) * L -
          477 / 100 +
        ((∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
          4 * ∑ k ∈ Finset.Ioc (0 : ℕ) 2557, Analysis.gammaResolventMangoldtWeight k) +
        ((7 / 3 : ℝ) * L + 12) / Real.sqrt (gammaMainCell260Scale : ℝ) +
        (105 / 2 : ℝ) * (gammaMainCell260Scale : ℝ) ^ (-9 / 16 : ℝ) +
        3 / ((gammaMainCell260Scale : ℝ) * Real.sqrt (gammaMainCell260Scale : ℝ)) <
      4 *
        ∑ k ∈ Finset.Ioc (0 : ℕ) 2557,
          Real.exp (-(k : ℝ) / (gammaMainCell260Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
            Real.sqrt (gammaMainCell260Scale : ℝ) := by
  apply
    gamma_gap_of_cell_caps (Finset.Ioc 0 2557) (gammaMainCell260Scale : ℝ) L
      (gammaFixed260Cell300Right : ℝ) (3645 / 100) (1751 / 100000) (gammaFixed260Main300Lower : ℝ)
      (3687 / 100) (47107 / 10000)
      (by norm_num only [gammaMainCell260Scale, Rat.cast_div, Rat.cast_ofNat]) (by norm_num only)
      (by norm_num only [gammaMainCell260Scale, Rat.cast_div, Rat.cast_ofNat])
      (by norm_num only [gammaFixed260Cell300Right, Rat.cast_div, Rat.cast_ofNat]) hL
      gammaFixed260_power_upper gammaFixed260Main300_actual_lower
      (gammaFixed260_principal_upper hRH) gammaFixed260Cell300_euler_lower (euler_mass_le_12372 hRH)
  norm_num only [gammaFixed260Cell300Right, gammaMainCell260Scale, gammaFixed260Main300Lower,
    Rat.cast_div, Rat.cast_ofNat]

/-- The right endpoint reached by the fixed-scale cutoff 2809. -/
def gammaFixed260Cell335Right : ℚ :=
  100

/-- The Euler prefix through 2809 exceeds the rational lower cap.
The center-row certificate gives the finite sum comparison. -/
theorem gammaFixed260Cell335_euler_lower :
    (9503 / 2000 : ℝ) ≤ ∑ n ∈ Finset.Ioc (0 : ℕ) 2809, Analysis.gammaResolventMangoldtWeight n := by
  have hc :
    (9503 / 2000 : ℚ) ≤
      ((centerRowsBelow 2809).map
          (fun r ↦ r.lo * Analysis.gammaFiniteEulerLower r.ratios)).sum := by
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using
    centerRowsBelow_euler_lower (by norm_num only : 2809 ≤ 50000) (9503 / 2000) hc

/-- Under RH, the fixed-scale principal, Euler and main bounds give a strict
Gamma gap up to the certified endpoint for cutoff 2809. -/
theorem gammaFixed260Cell335_gap (hRH : RiemannHypothesis) {L : ℝ}
    (hL : L ≤ (gammaFixed260Cell335Right : ℝ)) :
    (∑' k : ℕ,
              Real.exp (-(k : ℝ) / (gammaMainCell260Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
                Real.sqrt (gammaMainCell260Scale : ℝ)) +
            2 * (11783423 / 25000000 : ℝ) * L -
          477 / 100 +
        ((∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
          4 * ∑ k ∈ Finset.Ioc (0 : ℕ) 2809, Analysis.gammaResolventMangoldtWeight k) +
        ((7 / 3 : ℝ) * L + 12) / Real.sqrt (gammaMainCell260Scale : ℝ) +
        (105 / 2 : ℝ) * (gammaMainCell260Scale : ℝ) ^ (-9 / 16 : ℝ) +
        3 / ((gammaMainCell260Scale : ℝ) * Real.sqrt (gammaMainCell260Scale : ℝ)) <
      4 *
        ∑ k ∈ Finset.Ioc (0 : ℕ) 2809,
          Real.exp (-(k : ℝ) / (gammaMainCell260Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
            Real.sqrt (gammaMainCell260Scale : ℝ) := by
  apply
    gamma_gap_of_cell_caps (Finset.Ioc 0 2809) (gammaMainCell260Scale : ℝ) L
      (gammaFixed260Cell335Right : ℝ) (3645 / 100) (1751 / 100000) (gammaFixed260Main335Lower : ℝ)
      (3687 / 100) (9503 / 2000)
      (by norm_num only [gammaMainCell260Scale, Rat.cast_div, Rat.cast_ofNat]) (by norm_num only)
      (by norm_num only [gammaMainCell260Scale, Rat.cast_div, Rat.cast_ofNat])
      (by norm_num only [gammaFixed260Cell335Right, Rat.cast_div, Rat.cast_ofNat]) hL
      gammaFixed260_power_upper gammaFixed260Main335_actual_lower
      (gammaFixed260_principal_upper hRH) gammaFixed260Cell335_euler_lower (euler_mass_le_12372 hRH)
  norm_num only [gammaFixed260Cell335Right, gammaMainCell260Scale, gammaFixed260Main335Lower,
    Rat.cast_div, Rat.cast_ofNat]

end PseudoPrime.PrimeTestBounds.MillerRabin
