/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import all PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt81Checker
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevLcmBounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Chebyshev psi certificate on [26, 88) -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound

/-- LCM comparisons and the integer crossing check certify the cell starting at 26. -/
private theorem cell26 {x : ℝ} (ha : 26 ≤ x) (hb : x < 27) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (23567 : ℝ) / 1000 ≤ Chebyshev.psi 26 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 26) (k := 34) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 26 ≤ (24261 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 26) (k := 34) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨26, 27, 23567, 24261, 4130, 4208⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 27. -/
private theorem cell27 {x : ℝ} (ha : 27 ≤ x) (hb : x < 29) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (24953 : ℝ) / 1000 ≤ Chebyshev.psi 27 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 27) (k := 36) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 28 ≤ (25647 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 28) (k := 36) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨27, 29, 24953, 25647, 4208, 4361⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 29. -/
private theorem cell29 {x : ℝ} (ha : 29 ≤ x) (hb : x < 33) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (28419 : ℝ) / 1000 ≤ Chebyshev.psi 29 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 29) (k := 41) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 32 ≤ (33272 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 32) (k := 47) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨29, 33, 28419, 33272, 4361, 4653⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 33. -/
private theorem cell33 {x : ℝ} (ha : 33 ≤ x) (hb : x < 37) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (32577 : ℝ) / 1000 ≤ Chebyshev.psi 33 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 33) (k := 47) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 36 ≤ (33272 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 36) (k := 47) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨33, 37, 32577, 33272, 4653, 4927⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 37. -/
private theorem cell37 {x : ℝ} (ha : 37 ≤ x) (hb : x < 41) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (36043 : ℝ) / 1000 ≤ Chebyshev.psi 37 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 37) (k := 52) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 40 ≤ (36737 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 40) (k := 52) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨37, 41, 36043, 36737, 4927, 5186⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 41. -/
private theorem cell41 {x : ℝ} (ha : 41 ≤ x) (hb : x < 44) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (39509 : ℝ) / 1000 ≤ Chebyshev.psi 41 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 41) (k := 57) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 43 ≤ (44362 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 43) (k := 63) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨41, 44, 39509, 44362, 5186, 5372⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 44. -/
private theorem cell44 {x : ℝ} (ha : 44 ≤ x) (hb : x < 49) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (43668 : ℝ) / 1000 ≤ Chebyshev.psi 44 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 44) (k := 63) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 48 ≤ (47828 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 48) (k := 68) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨44, 49, 43668, 47828, 5372, 5670⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 49. -/
private theorem cell49 {x : ℝ} (ha : 49 ≤ x) (hb : x < 55) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (49213 : ℝ) / 1000 ≤ Chebyshev.psi 49 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 49) (k := 71) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 54 ≤ (54066 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 54) (k := 77) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨49, 55, 49213, 54066, 5670, 6007⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 55. -/
private theorem cell55 {x : ℝ} (ha : 55 ≤ x) (hb : x < 59) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (53372 : ℝ) / 1000 ≤ Chebyshev.psi 55 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 55) (k := 77) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 58 ≤ (54066 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 58) (k := 77) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨55, 59, 53372, 54066, 6007, 6221⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 59. -/
private theorem cell59 {x : ℝ} (ha : 59 ≤ x) (hb : x < 64) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (57531 : ℝ) / 1000 ≤ Chebyshev.psi 59 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 59) (k := 83) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 63 ≤ (61691 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 63) (k := 88) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨59, 64, 57531, 61691, 6221, 6480⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 64. -/
private theorem cell64 {x : ℝ} (ha : 64 ≤ x) (hb : x < 68) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (61690 : ℝ) / 1000 ≤ Chebyshev.psi 64 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 64) (k := 89) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 67 ≤ (66543 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 67) (k := 95) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨64, 68, 61690, 66543, 6480, 6679⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 68. -/
private theorem cell68 {x : ℝ} (ha : 68 ≤ x) (hb : x < 72) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (65848 : ℝ) / 1000 ≤ Chebyshev.psi 68 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 68) (k := 95) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 71 ≤ (71395 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 71) (k := 102) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨68, 72, 65848, 71395, 6679, 6873⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 72. -/
private theorem cell72 {x : ℝ} (ha : 72 ≤ x) (hb : x < 77) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (70701 : ℝ) / 1000 ≤ Chebyshev.psi 72 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 72) (k := 102) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 76 ≤ (75554 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 76) (k := 108) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨72, 77, 70701, 75554, 6873, 7107⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 77. -/
private theorem cell77 {x : ℝ} (ha : 77 ≤ x) (hb : x < 82) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (74859 : ℝ) / 1000 ≤ Chebyshev.psi 77 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 77) (k := 108) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 81 ≤ (81099 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 81) (k := 116) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨77, 82, 74859, 81099, 7107, 7334⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 82. -/
private theorem cell82 {x : ℝ} (ha : 82 ≤ x) (hb : x < 88) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (80405 : ℝ) / 1000 ≤ Chebyshev.psi 82 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 82) (k := 116) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 87 ≤ (85258 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 87) (k := 122) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨82, 88, 80405, 85258, 7334, 7598⟩ (by decide) hl hu ha hb

/-- The checked cells cover every real point in the half-open interval [26, 88). -/
theorem psi81_on_26_88 {x : ℝ} (ha : 26 ≤ x) (hb : x < 88) :
    |Chebyshev.psi x - x| / Real.sqrt x ≤ (81 / 100 : ℝ) := by
  have hx : 0 < x := by linarith only [ha]
  apply (div_le_iff₀ (Real.sqrt_pos.2 hx)).2
  by_cases h27 : x < 27
  · exact cell26 ha h27
  by_cases h29 : x < 29
  · exact cell27 (le_of_not_gt h27) h29
  by_cases h33 : x < 33
  · exact cell29 (le_of_not_gt h29) h33
  by_cases h37 : x < 37
  · exact cell33 (le_of_not_gt h33) h37
  by_cases h41 : x < 41
  · exact cell37 (le_of_not_gt h37) h41
  by_cases h44 : x < 44
  · exact cell41 (le_of_not_gt h41) h44
  by_cases h49 : x < 49
  · exact cell44 (le_of_not_gt h44) h49
  by_cases h55 : x < 55
  · exact cell49 (le_of_not_gt h49) h55
  by_cases h59 : x < 59
  · exact cell55 (le_of_not_gt h55) h59
  by_cases h64 : x < 64
  · exact cell59 (le_of_not_gt h59) h64
  by_cases h68 : x < 68
  · exact cell64 (le_of_not_gt h64) h68
  by_cases h72 : x < 72
  · exact cell68 (le_of_not_gt h68) h72
  by_cases h77 : x < 77
  · exact cell72 (le_of_not_gt h72) h77
  by_cases h82 : x < 82
  · exact cell77 (le_of_not_gt h77) h82
  exact cell82 (le_of_not_gt h82) hb

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound
