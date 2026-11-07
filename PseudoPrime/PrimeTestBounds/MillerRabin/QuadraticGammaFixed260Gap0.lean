/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaFixed260Main0
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaFixed260Principal

/-! # Fixed-scale Gamma gaps across multiple cells -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The right endpoint reached by the fixed-scale cutoff 1637. -/
def gammaFixed260Cell177Right : ℚ :=
  37738132792531 / 500000000000

/-- The Euler prefix through 1637 exceeds the rational lower cap.
The center-row certificate gives the finite sum comparison. -/
theorem gammaFixed260Cell177_euler_lower :
    (2832 / 625 : ℝ) ≤ ∑ n ∈ Finset.Ioc (0 : ℕ) 1637, Analysis.gammaResolventMangoldtWeight n := by
  have hc :
    (2832 / 625 : ℚ) ≤
      ((centerRowsBelow 1637).map
          (fun r ↦ r.lo * Analysis.gammaFiniteEulerLower r.ratios)).sum := by
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using
    centerRowsBelow_euler_lower (by norm_num only : 1637 ≤ 50000) (2832 / 625) hc

/-- Under RH, the fixed-scale principal, Euler and main bounds give a strict
Gamma gap up to the certified endpoint for cutoff 1637. -/
theorem gammaFixed260Cell177_gap (hRH : RiemannHypothesis) {L : ℝ}
    (hL : L ≤ (gammaFixed260Cell177Right : ℝ)) :
    (∑' k : ℕ,
              Real.exp (-(k : ℝ) / (gammaMainCell260Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
                Real.sqrt (gammaMainCell260Scale : ℝ)) +
            2 * (11783423 / 25000000 : ℝ) * L -
          477 / 100 +
        ((∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
          4 * ∑ k ∈ Finset.Ioc (0 : ℕ) 1637, Analysis.gammaResolventMangoldtWeight k) +
        ((7 / 3 : ℝ) * L + 12) / Real.sqrt (gammaMainCell260Scale : ℝ) +
        (105 / 2 : ℝ) * (gammaMainCell260Scale : ℝ) ^ (-9 / 16 : ℝ) +
        3 / ((gammaMainCell260Scale : ℝ) * Real.sqrt (gammaMainCell260Scale : ℝ)) <
      4 *
        ∑ k ∈ Finset.Ioc (0 : ℕ) 1637,
          Real.exp (-(k : ℝ) / (gammaMainCell260Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
            Real.sqrt (gammaMainCell260Scale : ℝ) := by
  apply
    gamma_gap_of_cell_caps (Finset.Ioc 0 1637) (gammaMainCell260Scale : ℝ) L
      (gammaFixed260Cell177Right : ℝ) (3645 / 100) (1751 / 100000) (gammaFixed260Main177Lower : ℝ)
      (3687 / 100) (2832 / 625)
      (by norm_num only [gammaMainCell260Scale, Rat.cast_div, Rat.cast_ofNat]) (by norm_num only)
      (by norm_num only [gammaMainCell260Scale, Rat.cast_div, Rat.cast_ofNat])
      (by norm_num only [gammaFixed260Cell177Right, Rat.cast_div, Rat.cast_ofNat]) hL
      gammaFixed260_power_upper gammaFixed260Main177_actual_lower
      (gammaFixed260_principal_upper hRH) gammaFixed260Cell177_euler_lower (euler_mass_le_12372 hRH)
  norm_num only [gammaFixed260Cell177Right, gammaMainCell260Scale, gammaFixed260Main177Lower,
    Rat.cast_div, Rat.cast_ofNat]

/-- The right endpoint reached by the fixed-scale cutoff 1709. -/
def gammaFixed260Cell186Right : ℚ :=
  77481180510711 / 1000000000000

/-- The Euler prefix through 1709 exceeds the rational lower cap.
The center-row certificate gives the finite sum comparison. -/
theorem gammaFixed260Cell186_euler_lower :
    (45469 / 10000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 1709, Analysis.gammaResolventMangoldtWeight n := by
  have hc :
    (45469 / 10000 : ℚ) ≤
      ((centerRowsBelow 1709).map
          (fun r ↦ r.lo * Analysis.gammaFiniteEulerLower r.ratios)).sum := by
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using
    centerRowsBelow_euler_lower (by norm_num only : 1709 ≤ 50000) (45469 / 10000) hc

/-- Under RH, the fixed-scale principal, Euler and main bounds give a strict
Gamma gap up to the certified endpoint for cutoff 1709. -/
theorem gammaFixed260Cell186_gap (hRH : RiemannHypothesis) {L : ℝ}
    (hL : L ≤ (gammaFixed260Cell186Right : ℝ)) :
    (∑' k : ℕ,
              Real.exp (-(k : ℝ) / (gammaMainCell260Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
                Real.sqrt (gammaMainCell260Scale : ℝ)) +
            2 * (11783423 / 25000000 : ℝ) * L -
          477 / 100 +
        ((∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
          4 * ∑ k ∈ Finset.Ioc (0 : ℕ) 1709, Analysis.gammaResolventMangoldtWeight k) +
        ((7 / 3 : ℝ) * L + 12) / Real.sqrt (gammaMainCell260Scale : ℝ) +
        (105 / 2 : ℝ) * (gammaMainCell260Scale : ℝ) ^ (-9 / 16 : ℝ) +
        3 / ((gammaMainCell260Scale : ℝ) * Real.sqrt (gammaMainCell260Scale : ℝ)) <
      4 *
        ∑ k ∈ Finset.Ioc (0 : ℕ) 1709,
          Real.exp (-(k : ℝ) / (gammaMainCell260Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
            Real.sqrt (gammaMainCell260Scale : ℝ) := by
  apply
    gamma_gap_of_cell_caps (Finset.Ioc 0 1709) (gammaMainCell260Scale : ℝ) L
      (gammaFixed260Cell186Right : ℝ) (3645 / 100) (1751 / 100000) (gammaFixed260Main186Lower : ℝ)
      (3687 / 100) (45469 / 10000)
      (by norm_num only [gammaMainCell260Scale, Rat.cast_div, Rat.cast_ofNat]) (by norm_num only)
      (by norm_num only [gammaMainCell260Scale, Rat.cast_div, Rat.cast_ofNat])
      (by norm_num only [gammaFixed260Cell186Right, Rat.cast_div, Rat.cast_ofNat]) hL
      gammaFixed260_power_upper gammaFixed260Main186_actual_lower
      (gammaFixed260_principal_upper hRH) gammaFixed260Cell186_euler_lower (euler_mass_le_12372 hRH)
  norm_num only [gammaFixed260Cell186Right, gammaMainCell260Scale, gammaFixed260Main186Lower,
    Rat.cast_div, Rat.cast_ofNat]

/-- The right endpoint reached by the fixed-scale cutoff 1801. -/
def gammaFixed260Cell198Right : ℚ :=
  80270376436973 / 1000000000000

/-- The Euler prefix through 1801 exceeds the rational lower cap.
The center-row certificate gives the finite sum comparison. -/
theorem gammaFixed260Cell198_euler_lower :
    (22841 / 5000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 1801, Analysis.gammaResolventMangoldtWeight n := by
  have hc :
    (22841 / 5000 : ℚ) ≤
      ((centerRowsBelow 1801).map
          (fun r ↦ r.lo * Analysis.gammaFiniteEulerLower r.ratios)).sum := by
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using
    centerRowsBelow_euler_lower (by norm_num only : 1801 ≤ 50000) (22841 / 5000) hc

/-- Under RH, the fixed-scale principal, Euler and main bounds give a strict
Gamma gap up to the certified endpoint for cutoff 1801. -/
theorem gammaFixed260Cell198_gap (hRH : RiemannHypothesis) {L : ℝ}
    (hL : L ≤ (gammaFixed260Cell198Right : ℝ)) :
    (∑' k : ℕ,
              Real.exp (-(k : ℝ) / (gammaMainCell260Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
                Real.sqrt (gammaMainCell260Scale : ℝ)) +
            2 * (11783423 / 25000000 : ℝ) * L -
          477 / 100 +
        ((∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
          4 * ∑ k ∈ Finset.Ioc (0 : ℕ) 1801, Analysis.gammaResolventMangoldtWeight k) +
        ((7 / 3 : ℝ) * L + 12) / Real.sqrt (gammaMainCell260Scale : ℝ) +
        (105 / 2 : ℝ) * (gammaMainCell260Scale : ℝ) ^ (-9 / 16 : ℝ) +
        3 / ((gammaMainCell260Scale : ℝ) * Real.sqrt (gammaMainCell260Scale : ℝ)) <
      4 *
        ∑ k ∈ Finset.Ioc (0 : ℕ) 1801,
          Real.exp (-(k : ℝ) / (gammaMainCell260Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
            Real.sqrt (gammaMainCell260Scale : ℝ) := by
  apply
    gamma_gap_of_cell_caps (Finset.Ioc 0 1801) (gammaMainCell260Scale : ℝ) L
      (gammaFixed260Cell198Right : ℝ) (3645 / 100) (1751 / 100000) (gammaFixed260Main198Lower : ℝ)
      (3687 / 100) (22841 / 5000)
      (by norm_num only [gammaMainCell260Scale, Rat.cast_div, Rat.cast_ofNat]) (by norm_num only)
      (by norm_num only [gammaMainCell260Scale, Rat.cast_div, Rat.cast_ofNat])
      (by norm_num only [gammaFixed260Cell198Right, Rat.cast_div, Rat.cast_ofNat]) hL
      gammaFixed260_power_upper gammaFixed260Main198_actual_lower
      (gammaFixed260_principal_upper hRH) gammaFixed260Cell198_euler_lower (euler_mass_le_12372 hRH)
  norm_num only [gammaFixed260Cell198Right, gammaMainCell260Scale, gammaFixed260Main198Lower,
    Rat.cast_div, Rat.cast_ofNat]

/-- The right endpoint reached by the fixed-scale cutoff 1933. -/
def gammaFixed260Cell215Right : ℚ :=
  10455759975567 / 125000000000

/-- The Euler prefix through 1933 exceeds the rational lower cap.
The center-row certificate gives the finite sum comparison. -/
theorem gammaFixed260Cell215_euler_lower :
    (45957 / 10000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 1933, Analysis.gammaResolventMangoldtWeight n := by
  have hc :
    (45957 / 10000 : ℚ) ≤
      ((centerRowsBelow 1933).map
          (fun r ↦ r.lo * Analysis.gammaFiniteEulerLower r.ratios)).sum := by
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using
    centerRowsBelow_euler_lower (by norm_num only : 1933 ≤ 50000) (45957 / 10000) hc

/-- Under RH, the fixed-scale principal, Euler and main bounds give a strict
Gamma gap up to the certified endpoint for cutoff 1933. -/
theorem gammaFixed260Cell215_gap (hRH : RiemannHypothesis) {L : ℝ}
    (hL : L ≤ (gammaFixed260Cell215Right : ℝ)) :
    (∑' k : ℕ,
              Real.exp (-(k : ℝ) / (gammaMainCell260Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
                Real.sqrt (gammaMainCell260Scale : ℝ)) +
            2 * (11783423 / 25000000 : ℝ) * L -
          477 / 100 +
        ((∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
          4 * ∑ k ∈ Finset.Ioc (0 : ℕ) 1933, Analysis.gammaResolventMangoldtWeight k) +
        ((7 / 3 : ℝ) * L + 12) / Real.sqrt (gammaMainCell260Scale : ℝ) +
        (105 / 2 : ℝ) * (gammaMainCell260Scale : ℝ) ^ (-9 / 16 : ℝ) +
        3 / ((gammaMainCell260Scale : ℝ) * Real.sqrt (gammaMainCell260Scale : ℝ)) <
      4 *
        ∑ k ∈ Finset.Ioc (0 : ℕ) 1933,
          Real.exp (-(k : ℝ) / (gammaMainCell260Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
            Real.sqrt (gammaMainCell260Scale : ℝ) := by
  apply
    gamma_gap_of_cell_caps (Finset.Ioc 0 1933) (gammaMainCell260Scale : ℝ) L
      (gammaFixed260Cell215Right : ℝ) (3645 / 100) (1751 / 100000) (gammaFixed260Main215Lower : ℝ)
      (3687 / 100) (45957 / 10000)
      (by norm_num only [gammaMainCell260Scale, Rat.cast_div, Rat.cast_ofNat]) (by norm_num only)
      (by norm_num only [gammaMainCell260Scale, Rat.cast_div, Rat.cast_ofNat])
      (by norm_num only [gammaFixed260Cell215Right, Rat.cast_div, Rat.cast_ofNat]) hL
      gammaFixed260_power_upper gammaFixed260Main215_actual_lower
      (gammaFixed260_principal_upper hRH) gammaFixed260Cell215_euler_lower (euler_mass_le_12372 hRH)
  norm_num only [gammaFixed260Cell215Right, gammaMainCell260Scale, gammaFixed260Main215Lower,
    Rat.cast_div, Rat.cast_ofNat]

end PseudoPrime.PrimeTestBounds.MillerRabin
