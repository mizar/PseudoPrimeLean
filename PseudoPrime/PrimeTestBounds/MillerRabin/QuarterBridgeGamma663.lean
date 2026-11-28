/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterGammaEndpoints656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterGammaEndpoints656
import PseudoPrime.Analysis.LogTaylorBounds

/-! # Gamma-pole bound for the quarter-square bridge -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private theorem first_rectangle_bridge {z : ℝ} (hl : 14.211 ≤ z) (hu : z ≤ 14.236) :
    0.02379 ≤ quarterGammaFirst656 z := by
  have ht :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1000000 / 199) (j := 13) (n := 48) (lo := 8)
        (hi := 8.5266) (by decide +kernel)).2
  have hf :=
    (Analysis.rationalLogIntervalCheck_sound (N := 100000 / 81) (j := 11) (n := 48) (lo := 7.118)
        (hi := 8) (by decide +kernel)).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at ht hf
  have htail : Real.exp (-(3 / 5 : ℝ) * 14.211) ≤ 0.000199 := by
    rw [neg_mul]
    apply exp_neg_le_of_log_inv (by norm_num only)
    norm_num only at ht ⊢
    linarith only [ht]
  have hfront : 0.00081 ≤ Real.exp (-(1 / 2 : ℝ) * 14.236) := by
    rw [neg_mul]
    apply le_exp_neg_of_log_inv (by norm_num only)
    norm_num only at hf ⊢
    linarith only [hf]
  have hm :=
    first_moment_lower_of_exp htail (m := 2189)
      (by norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat, Nat.cast_one])
      (by norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat, Nat.cast_one])
  exact
    first_rectangle_lower (c := 0.02379) (by norm_num only) hl hu hfront hm (by norm_num only)
      (by norm_num only)

/-- The first Gamma pole gives a uniform credit for radii between 328
and 332, including all three quarter-square bridge intervals. -/
theorem quarter_gamma_bridge_663 {r : ℝ} (hr : r ∈ Set.Icc 328 332) :
    (centralGammaPair656 (1 : DirichletCharacter ℂ 1) (r ^ 2)).re ≤
      -2.16 * quarterWeight656 (r ^ 2) 1 - 0.02379 := by
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound (N := 328) (j := 9) (n := 32) (lo := 5.793) (hi := 6)
        (by decide +kernel)).1
  have hu :=
    (Analysis.rationalLogIntervalCheck_sound (N := 332) (j := 9) (n := 32) (lo := 5) (hi := 5.8055)
        (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl hu
  have hr₀ : 0 < r := (by norm_num only : (0 : ℝ) < 328).trans_le hr.1
  have hlo := Real.log_le_log (by norm_num only : (0 : ℝ) < 328) hr.1
  have hup := Real.log_le_log hr₀ hr.2
  have hfirst : 0.02379 ≤ quarterGammaFirst656 (Real.log (r ^ 2) + 21 / 8) := by
    rw [Real.log_pow]
    exact first_rectangle_bridge (by linarith only [hl, hlo]) (by linarith only [hu, hup])
  exact
    (quarter_principal_gamma_upper_656 ((by norm_num only : (322 : ℝ) ≤ 328).trans hr.1)).trans
      (sub_le_sub_left hfirst _)

end PseudoPrime.PrimeTestBounds.MillerRabin
