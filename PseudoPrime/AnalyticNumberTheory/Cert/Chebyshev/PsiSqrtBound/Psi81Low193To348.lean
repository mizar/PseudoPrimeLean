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

/-! # Chebyshev psi certificate on [193, 348) -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound

/-- LCM comparisons and the integer crossing check certify the cell starting at 193. -/
private theorem cell193 {x : ℝ} (ha : 193 ≤ x) (hb : x < 199) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (195467 : ℝ) / 1000 ≤ Chebyshev.psi 193 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 193) (k := 282) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 198 ≤ (201013 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 198) (k := 289) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨193, 199, 195467, 201013, 11252, 11426⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 199. -/
private theorem cell199 {x : ℝ} (ha : 199 ≤ x) (hb : x < 211) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (205864 : ℝ) / 1000 ≤ Chebyshev.psi 199 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 199) (k := 297) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 210 ≤ (206558 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 210) (k := 297) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨199, 211, 205864, 206558, 11426, 11765⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 211. -/
private theorem cell211 {x : ℝ} (ha : 211 ≤ x) (hb : x < 223) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (211409 : ℝ) / 1000 ≤ Chebyshev.psi 211 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 211) (k := 305) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 222 ≤ (212104 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 222) (k := 305) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨211, 223, 211409, 212104, 11765, 12095⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 223. -/
private theorem cell223 {x : ℝ} (ha : 223 ≤ x) (hb : x < 228) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (216261 : ℝ) / 1000 ≤ Chebyshev.psi 223 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 223) (k := 312) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 227 ≤ (222501 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 227) (k := 320) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨223, 228, 216261, 222501, 12095, 12230⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 228. -/
private theorem cell228 {x : ℝ} (ha : 228 ≤ x) (hb : x < 234) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (221807 : ℝ) / 1000 ≤ Chebyshev.psi 228 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 228) (k := 320) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 233 ≤ (233591 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 233) (k := 336) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨228, 234, 221807, 233591, 12230, 12390⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 234. -/
private theorem cell234 {x : ℝ} (ha : 234 ≤ x) (hb : x < 245) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (232897 : ℝ) / 1000 ≤ Chebyshev.psi 234 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 234) (k := 336) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 244 ≤ (245375 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 244) (k := 353) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨234, 245, 232897, 245375, 12390, 12678⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 245. -/
private theorem cell245 {x : ℝ} (ha : 245 ≤ x) (hb : x < 257) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (244680 : ℝ) / 1000 ≤ Chebyshev.psi 245 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 245) (k := 353) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 256 ≤ (251613 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 256) (k := 362) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨245, 257, 244680, 251613, 12678, 12985⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 257. -/
private theorem cell257 {x : ℝ} (ha : 257 ≤ x) (hb : x < 269) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (256464 : ℝ) / 1000 ≤ Chebyshev.psi 257 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 257) (k := 370) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 268 ≤ (262703 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 268) (k := 378) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨257, 269, 256464, 262703, 12985, 13284⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 269. -/
private theorem cell269 {x : ℝ} (ha : 269 ≤ x) (hb : x < 281) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (267554 : ℝ) / 1000 ≤ Chebyshev.psi 269 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 269) (k := 386) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 280 ≤ (280032 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 280) (k := 403) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨269, 281, 267554, 280032, 13284, 13578⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 281. -/
private theorem cell281 {x : ℝ} (ha : 281 ≤ x) (hb : x < 293) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (284883 : ℝ) / 1000 ≤ Chebyshev.psi 281 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 281) (k := 411) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 292 ≤ (293895 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 292) (k := 423) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨281, 293, 284883, 293895, 13578, 13864⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 293. -/
private theorem cell293 {x : ℝ} (ha : 293 ≤ x) (hb : x < 311) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (298746 : ℝ) / 1000 ≤ Chebyshev.psi 293 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 293) (k := 431) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 310 ≤ (304985 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 310) (k := 439) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨293, 311, 298746, 304985, 13864, 14284⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 311. -/
private theorem cell311 {x : ℝ} (ha : 311 ≤ x) (hb : x < 325) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (310529 : ℝ) / 1000 ≤ Chebyshev.psi 311 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 311) (k := 448) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 324 ≤ (322314 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 324) (k := 464) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨311, 325, 310529, 322314, 14284, 14602⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 325. -/
private theorem cell325 {x : ℝ} (ha : 325 ≤ x) (hb : x < 336) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (321620 : ℝ) / 1000 ≤ Chebyshev.psi 325 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 325) (k := 464) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 335 ≤ (328552 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 335) (k := 473) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨325, 336, 321620, 328552, 14602, 14847⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 336. -/
private theorem cell336 {x : ℝ} (ha : 336 ≤ x) (hb : x < 342) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (327858 : ℝ) / 1000 ≤ Chebyshev.psi 336 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 336) (k := 473) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 341 ≤ (334097 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 341) (k := 481) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨336, 342, 327858, 334097, 14847, 14979⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 342. -/
private theorem cell342 {x : ℝ} (ha : 342 ≤ x) (hb : x < 348) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (333403 : ℝ) / 1000 ≤ Chebyshev.psi 342 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 342) (k := 481) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 347 ≤ (341722 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 347) (k := 492) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨342, 348, 333403, 341722, 14979, 15110⟩ (by decide) hl hu ha hb

/-- The checked cells cover every real point in the half-open interval [193, 348). -/
theorem psi81_on_193_348 {x : ℝ} (ha : 193 ≤ x) (hb : x < 348) :
    |Chebyshev.psi x - x| / Real.sqrt x ≤ (81 / 100 : ℝ) := by
  have hx : 0 < x := by linarith only [ha]
  apply (div_le_iff₀ (Real.sqrt_pos.2 hx)).2
  by_cases h199 : x < 199
  · exact cell193 ha h199
  by_cases h211 : x < 211
  · exact cell199 (le_of_not_gt h199) h211
  by_cases h223 : x < 223
  · exact cell211 (le_of_not_gt h211) h223
  by_cases h228 : x < 228
  · exact cell223 (le_of_not_gt h223) h228
  by_cases h234 : x < 234
  · exact cell228 (le_of_not_gt h228) h234
  by_cases h245 : x < 245
  · exact cell234 (le_of_not_gt h234) h245
  by_cases h257 : x < 257
  · exact cell245 (le_of_not_gt h245) h257
  by_cases h269 : x < 269
  · exact cell257 (le_of_not_gt h257) h269
  by_cases h281 : x < 281
  · exact cell269 (le_of_not_gt h269) h281
  by_cases h293 : x < 293
  · exact cell281 (le_of_not_gt h281) h293
  by_cases h311 : x < 311
  · exact cell293 (le_of_not_gt h293) h311
  by_cases h325 : x < 325
  · exact cell311 (le_of_not_gt h311) h325
  by_cases h336 : x < 336
  · exact cell325 (le_of_not_gt h325) h336
  by_cases h342 : x < 342
  · exact cell336 (le_of_not_gt h336) h342
  exact cell342 (le_of_not_gt h342) hb

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound
