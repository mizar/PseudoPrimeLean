/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaFixed92Main2
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaFixed92Power

/-! # Fixed-scale Gamma gaps across multiple cells -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The right endpoint reached by the fixed-scale cutoff 1331. -/
def gammaFixed92Cell134Right : ℚ :=
  34556716665023 / 500000000000

/-- The Euler prefix through 1331 exceeds the rational lower cap.
The center-row certificate gives the finite sum comparison. -/
theorem gammaFixed92Cell134_euler_lower :
    (44437 / 10000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 1331, Analysis.gammaResolventMangoldtWeight n := by
  have hc :
    (44437 / 10000 : ℚ) ≤
      ((centerRowsBelow 1331).map
          (fun r ↦ r.lo * Analysis.gammaFiniteEulerLower r.ratios)).sum := by
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using
    centerRowsBelow_euler_lower (by norm_num only : 1331 ≤ 50000) (44437 / 10000) hc

/-- Under RH, the fixed-scale principal, Euler and main bounds give a strict
Gamma gap up to the certified endpoint for cutoff 1331. -/
theorem gammaFixed92Cell134_gap (hRH : RiemannHypothesis) {L : ℝ}
    (hL : L ≤ (gammaFixed92Cell134Right : ℝ)) :
    (∑' k : ℕ,
              Real.exp (-(k : ℝ) / (gammaMainCell92Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
                Real.sqrt (gammaMainCell92Scale : ℝ)) +
            2 * (11783423 / 25000000 : ℝ) * L -
          477 / 100 +
        ((∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
          4 * ∑ k ∈ Finset.Ioc (0 : ℕ) 1331, Analysis.gammaResolventMangoldtWeight k) +
        ((7 / 3 : ℝ) * L + 12) / Real.sqrt (gammaMainCell92Scale : ℝ) +
        (105 / 2 : ℝ) * (gammaMainCell92Scale : ℝ) ^ (-9 / 16 : ℝ) +
        3 / ((gammaMainCell92Scale : ℝ) * Real.sqrt (gammaMainCell92Scale : ℝ)) <
      4 *
        ∑ k ∈ Finset.Ioc (0 : ℕ) 1331,
          Real.exp (-(k : ℝ) / (gammaMainCell92Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
            Real.sqrt (gammaMainCell92Scale : ℝ) := by
  apply
    gamma_gap_of_cell_caps (Finset.Ioc 0 1331) (gammaMainCell92Scale : ℝ) L
      (gammaFixed92Cell134Right : ℝ) (253 / 10) (33 / 1250) (gammaFixed92Main134Lower : ℝ)
      (25238049 / 1000000) (44437 / 10000)
      (by norm_num only [gammaMainCell92Scale, Rat.cast_div, Rat.cast_ofNat]) (by norm_num only)
      (by norm_num only [gammaMainCell92Scale, Rat.cast_div, Rat.cast_ofNat])
      (by norm_num only [gammaFixed92Cell134Right, Rat.cast_div, Rat.cast_ofNat]) hL
      gammaFixed92_power_upper gammaFixed92Main134_actual_lower
      (by
        simpa only [gammaUpperCell92Scale, gammaMainCell92Scale] using gammaCell92_principal_upper)
      gammaFixed92Cell134_euler_lower (euler_mass_le_12372 hRH)
  norm_num only [gammaFixed92Cell134Right, gammaMainCell92Scale, gammaFixed92Main134Lower,
    Rat.cast_div, Rat.cast_ofNat]

/-- The right endpoint reached by the fixed-scale cutoff 1433. -/
def gammaFixed92Cell145Right : ℚ :=
  70545493595741 / 1000000000000

/-- The Euler prefix through 1433 exceeds the rational lower cap.
The center-row certificate gives the finite sum comparison. -/
theorem gammaFixed92Cell145_euler_lower :
    (11167 / 2500 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 1433, Analysis.gammaResolventMangoldtWeight n := by
  have hc :
    (11167 / 2500 : ℚ) ≤
      ((centerRowsBelow 1433).map
          (fun r ↦ r.lo * Analysis.gammaFiniteEulerLower r.ratios)).sum := by
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using
    centerRowsBelow_euler_lower (by norm_num only : 1433 ≤ 50000) (11167 / 2500) hc

/-- Under RH, the fixed-scale principal, Euler and main bounds give a strict
Gamma gap up to the certified endpoint for cutoff 1433. -/
theorem gammaFixed92Cell145_gap (hRH : RiemannHypothesis) {L : ℝ}
    (hL : L ≤ (gammaFixed92Cell145Right : ℝ)) :
    (∑' k : ℕ,
              Real.exp (-(k : ℝ) / (gammaMainCell92Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
                Real.sqrt (gammaMainCell92Scale : ℝ)) +
            2 * (11783423 / 25000000 : ℝ) * L -
          477 / 100 +
        ((∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
          4 * ∑ k ∈ Finset.Ioc (0 : ℕ) 1433, Analysis.gammaResolventMangoldtWeight k) +
        ((7 / 3 : ℝ) * L + 12) / Real.sqrt (gammaMainCell92Scale : ℝ) +
        (105 / 2 : ℝ) * (gammaMainCell92Scale : ℝ) ^ (-9 / 16 : ℝ) +
        3 / ((gammaMainCell92Scale : ℝ) * Real.sqrt (gammaMainCell92Scale : ℝ)) <
      4 *
        ∑ k ∈ Finset.Ioc (0 : ℕ) 1433,
          Real.exp (-(k : ℝ) / (gammaMainCell92Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
            Real.sqrt (gammaMainCell92Scale : ℝ) := by
  apply
    gamma_gap_of_cell_caps (Finset.Ioc 0 1433) (gammaMainCell92Scale : ℝ) L
      (gammaFixed92Cell145Right : ℝ) (253 / 10) (33 / 1250) (gammaFixed92Main145Lower : ℝ)
      (25238049 / 1000000) (11167 / 2500)
      (by norm_num only [gammaMainCell92Scale, Rat.cast_div, Rat.cast_ofNat]) (by norm_num only)
      (by norm_num only [gammaMainCell92Scale, Rat.cast_div, Rat.cast_ofNat])
      (by norm_num only [gammaFixed92Cell145Right, Rat.cast_div, Rat.cast_ofNat]) hL
      gammaFixed92_power_upper gammaFixed92Main145_actual_lower
      (by
        simpa only [gammaUpperCell92Scale, gammaMainCell92Scale] using gammaCell92_principal_upper)
      gammaFixed92Cell145_euler_lower (euler_mass_le_12372 hRH)
  norm_num only [gammaFixed92Cell145Right, gammaMainCell92Scale, gammaFixed92Main145Lower,
    Rat.cast_div, Rat.cast_ofNat]

/-- The right endpoint reached by the fixed-scale cutoff 1493. -/
def gammaFixed92Cell156Right : ℚ :=
  8993632006407 / 125000000000

/-- The Euler prefix through 1493 exceeds the rational lower cap.
The center-row certificate gives the finite sum comparison. -/
theorem gammaFixed92Cell156_euler_lower :
    (44899 / 10000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 1493, Analysis.gammaResolventMangoldtWeight n := by
  have hc :
    (44899 / 10000 : ℚ) ≤
      ((centerRowsBelow 1493).map
          (fun r ↦ r.lo * Analysis.gammaFiniteEulerLower r.ratios)).sum := by
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using
    centerRowsBelow_euler_lower (by norm_num only : 1493 ≤ 50000) (44899 / 10000) hc

/-- Under RH, the fixed-scale principal, Euler and main bounds give a strict
Gamma gap up to the certified endpoint for cutoff 1493. -/
theorem gammaFixed92Cell156_gap (hRH : RiemannHypothesis) {L : ℝ}
    (hL : L ≤ (gammaFixed92Cell156Right : ℝ)) :
    (∑' k : ℕ,
              Real.exp (-(k : ℝ) / (gammaMainCell92Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
                Real.sqrt (gammaMainCell92Scale : ℝ)) +
            2 * (11783423 / 25000000 : ℝ) * L -
          477 / 100 +
        ((∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
          4 * ∑ k ∈ Finset.Ioc (0 : ℕ) 1493, Analysis.gammaResolventMangoldtWeight k) +
        ((7 / 3 : ℝ) * L + 12) / Real.sqrt (gammaMainCell92Scale : ℝ) +
        (105 / 2 : ℝ) * (gammaMainCell92Scale : ℝ) ^ (-9 / 16 : ℝ) +
        3 / ((gammaMainCell92Scale : ℝ) * Real.sqrt (gammaMainCell92Scale : ℝ)) <
      4 *
        ∑ k ∈ Finset.Ioc (0 : ℕ) 1493,
          Real.exp (-(k : ℝ) / (gammaMainCell92Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
            Real.sqrt (gammaMainCell92Scale : ℝ) := by
  apply
    gamma_gap_of_cell_caps (Finset.Ioc 0 1493) (gammaMainCell92Scale : ℝ) L
      (gammaFixed92Cell156Right : ℝ) (253 / 10) (33 / 1250) (gammaFixed92Main156Lower : ℝ)
      (25238049 / 1000000) (44899 / 10000)
      (by norm_num only [gammaMainCell92Scale, Rat.cast_div, Rat.cast_ofNat]) (by norm_num only)
      (by norm_num only [gammaMainCell92Scale, Rat.cast_div, Rat.cast_ofNat])
      (by norm_num only [gammaFixed92Cell156Right, Rat.cast_div, Rat.cast_ofNat]) hL
      gammaFixed92_power_upper gammaFixed92Main156_actual_lower
      (by
        simpa only [gammaUpperCell92Scale, gammaMainCell92Scale] using gammaCell92_principal_upper)
      gammaFixed92Cell156_euler_lower (euler_mass_le_12372 hRH)
  norm_num only [gammaFixed92Cell156Right, gammaMainCell92Scale, gammaFixed92Main156Lower,
    Rat.cast_div, Rat.cast_ofNat]

/-- The right endpoint reached by the fixed-scale cutoff 1553. -/
def gammaFixed92Cell163Right : ℚ :=
  72640668132023 / 1000000000000

/-- The Euler prefix through 1553 exceeds the rational lower cap.
The center-row certificate gives the finite sum comparison. -/
theorem gammaFixed92Cell163_euler_lower :
    (45041 / 10000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 1553, Analysis.gammaResolventMangoldtWeight n := by
  have hc :
    (45041 / 10000 : ℚ) ≤
      ((centerRowsBelow 1553).map
          (fun r ↦ r.lo * Analysis.gammaFiniteEulerLower r.ratios)).sum := by
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using
    centerRowsBelow_euler_lower (by norm_num only : 1553 ≤ 50000) (45041 / 10000) hc

/-- Under RH, the fixed-scale principal, Euler and main bounds give a strict
Gamma gap up to the certified endpoint for cutoff 1553. -/
theorem gammaFixed92Cell163_gap (hRH : RiemannHypothesis) {L : ℝ}
    (hL : L ≤ (gammaFixed92Cell163Right : ℝ)) :
    (∑' k : ℕ,
              Real.exp (-(k : ℝ) / (gammaMainCell92Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
                Real.sqrt (gammaMainCell92Scale : ℝ)) +
            2 * (11783423 / 25000000 : ℝ) * L -
          477 / 100 +
        ((∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
          4 * ∑ k ∈ Finset.Ioc (0 : ℕ) 1553, Analysis.gammaResolventMangoldtWeight k) +
        ((7 / 3 : ℝ) * L + 12) / Real.sqrt (gammaMainCell92Scale : ℝ) +
        (105 / 2 : ℝ) * (gammaMainCell92Scale : ℝ) ^ (-9 / 16 : ℝ) +
        3 / ((gammaMainCell92Scale : ℝ) * Real.sqrt (gammaMainCell92Scale : ℝ)) <
      4 *
        ∑ k ∈ Finset.Ioc (0 : ℕ) 1553,
          Real.exp (-(k : ℝ) / (gammaMainCell92Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
            Real.sqrt (gammaMainCell92Scale : ℝ) := by
  apply
    gamma_gap_of_cell_caps (Finset.Ioc 0 1553) (gammaMainCell92Scale : ℝ) L
      (gammaFixed92Cell163Right : ℝ) (253 / 10) (33 / 1250) (gammaFixed92Main163Lower : ℝ)
      (25238049 / 1000000) (45041 / 10000)
      (by norm_num only [gammaMainCell92Scale, Rat.cast_div, Rat.cast_ofNat]) (by norm_num only)
      (by norm_num only [gammaMainCell92Scale, Rat.cast_div, Rat.cast_ofNat])
      (by norm_num only [gammaFixed92Cell163Right, Rat.cast_div, Rat.cast_ofNat]) hL
      gammaFixed92_power_upper gammaFixed92Main163_actual_lower
      (by
        simpa only [gammaUpperCell92Scale, gammaMainCell92Scale] using gammaCell92_principal_upper)
      gammaFixed92Cell163_euler_lower (euler_mass_le_12372 hRH)
  norm_num only [gammaFixed92Cell163Right, gammaMainCell92Scale, gammaFixed92Main163Lower,
    Rat.cast_div, Rat.cast_ofNat]

/-- The right endpoint reached by the fixed-scale cutoff 1583. -/
def gammaFixed92Cell168Right : ℚ :=
  18308695566133 / 250000000000

/-- The Euler prefix through 1583 exceeds the rational lower cap.
The center-row certificate gives the finite sum comparison. -/
theorem gammaFixed92Cell168_euler_lower :
    (45139 / 10000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 1583, Analysis.gammaResolventMangoldtWeight n := by
  have hc :
    (45139 / 10000 : ℚ) ≤
      ((centerRowsBelow 1583).map
          (fun r ↦ r.lo * Analysis.gammaFiniteEulerLower r.ratios)).sum := by
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using
    centerRowsBelow_euler_lower (by norm_num only : 1583 ≤ 50000) (45139 / 10000) hc

/-- Under RH, the fixed-scale principal, Euler and main bounds give a strict
Gamma gap up to the certified endpoint for cutoff 1583. -/
theorem gammaFixed92Cell168_gap (hRH : RiemannHypothesis) {L : ℝ}
    (hL : L ≤ (gammaFixed92Cell168Right : ℝ)) :
    (∑' k : ℕ,
              Real.exp (-(k : ℝ) / (gammaMainCell92Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
                Real.sqrt (gammaMainCell92Scale : ℝ)) +
            2 * (11783423 / 25000000 : ℝ) * L -
          477 / 100 +
        ((∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
          4 * ∑ k ∈ Finset.Ioc (0 : ℕ) 1583, Analysis.gammaResolventMangoldtWeight k) +
        ((7 / 3 : ℝ) * L + 12) / Real.sqrt (gammaMainCell92Scale : ℝ) +
        (105 / 2 : ℝ) * (gammaMainCell92Scale : ℝ) ^ (-9 / 16 : ℝ) +
        3 / ((gammaMainCell92Scale : ℝ) * Real.sqrt (gammaMainCell92Scale : ℝ)) <
      4 *
        ∑ k ∈ Finset.Ioc (0 : ℕ) 1583,
          Real.exp (-(k : ℝ) / (gammaMainCell92Scale : ℝ)) * ArithmeticFunction.vonMangoldt k /
            Real.sqrt (gammaMainCell92Scale : ℝ) := by
  apply
    gamma_gap_of_cell_caps (Finset.Ioc 0 1583) (gammaMainCell92Scale : ℝ) L
      (gammaFixed92Cell168Right : ℝ) (253 / 10) (33 / 1250) (gammaFixed92Main168Lower : ℝ)
      (25238049 / 1000000) (45139 / 10000)
      (by norm_num only [gammaMainCell92Scale, Rat.cast_div, Rat.cast_ofNat]) (by norm_num only)
      (by norm_num only [gammaMainCell92Scale, Rat.cast_div, Rat.cast_ofNat])
      (by norm_num only [gammaFixed92Cell168Right, Rat.cast_div, Rat.cast_ofNat]) hL
      gammaFixed92_power_upper gammaFixed92Main168_actual_lower
      (by
        simpa only [gammaUpperCell92Scale, gammaMainCell92Scale] using gammaCell92_principal_upper)
      gammaFixed92Cell168_euler_lower (euler_mass_le_12372 hRH)
  norm_num only [gammaFixed92Cell168Right, gammaMainCell92Scale, gammaFixed92Main168Lower,
    Rat.cast_div, Rat.cast_ofNat]

end PseudoPrime.PrimeTestBounds.MillerRabin
