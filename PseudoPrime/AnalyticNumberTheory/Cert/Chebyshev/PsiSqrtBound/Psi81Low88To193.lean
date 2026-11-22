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

/-! # Chebyshev psi certificate on [88, 193) -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound

/-- LCM comparisons and the integer crossing check certify the cell starting at 88. -/
private theorem cell88 {x : ℝ} (ha : 88 ≤ x) (hb : x < 92) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (84563 : ℝ) / 1000 ≤ Chebyshev.psi 88 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 88) (k := 122) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 91 ≤ (90110 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 91) (k := 129) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨88, 92, 84563, 90110, 7598, 7769⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 92. -/
private theorem cell92 {x : ℝ} (ha : 92 ≤ x) (hb : x < 97) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (89415 : ℝ) / 1000 ≤ Chebyshev.psi 92 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 92) (k := 129) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 96 ≤ (90110 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 96) (k := 129) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨92, 97, 89415, 90110, 7769, 7977⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 97. -/
private theorem cell97 {x : ℝ} (ha : 97 ≤ x) (hb : x < 101) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (93574 : ℝ) / 1000 ≤ Chebyshev.psi 97 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 97) (k := 135) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 100 ≤ (94269 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 100) (k := 135) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨97, 101, 93574, 94269, 7977, 8140⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 101. -/
private theorem cell101 {x : ℝ} (ha : 101 ≤ x) (hb : x < 106) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (98426 : ℝ) / 1000 ≤ Chebyshev.psi 101 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 101) (k := 142) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 105 ≤ (103973 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 105) (k := 149) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨101, 106, 98426, 103973, 8140, 8339⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 106. -/
private theorem cell106 {x : ℝ} (ha : 106 ≤ x) (hb : x < 111) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (103278 : ℝ) / 1000 ≤ Chebyshev.psi 106 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 106) (k := 149) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 110 ≤ (112983 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 110) (k := 162) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨106, 111, 103278, 112983, 8339, 8533⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 111. -/
private theorem cell111 {x : ℝ} (ha : 111 ≤ x) (hb : x < 121) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (112289 : ℝ) / 1000 ≤ Chebyshev.psi 111 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 111) (k := 162) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 120 ≤ (117836 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 120) (k := 169) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨111, 121, 112289, 117836, 8533, 8910⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 121. -/
private theorem cell121 {x : ℝ} (ha : 121 ≤ x) (hb : x < 128) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (119221 : ℝ) / 1000 ≤ Chebyshev.psi 121 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 121) (k := 172) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 127 ≤ (126846 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 127) (k := 182) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨121, 128, 119221, 126846, 8910, 9164⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 128. -/
private theorem cell128 {x : ℝ} (ha : 128 ≤ x) (hb : x < 136) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (126845 : ℝ) / 1000 ≤ Chebyshev.psi 128 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 128) (k := 183) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 135 ≤ (132392 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 135) (k := 190) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨128, 136, 126845, 132392, 9164, 9446⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 136. -/
private theorem cell136 {x : ℝ} (ha : 136 ≤ x) (hb : x < 141) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (131697 : ℝ) / 1000 ≤ Chebyshev.psi 136 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 136) (k := 190) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 140 ≤ (142096 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 140) (k := 204) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨136, 141, 131697, 142096, 9446, 9618⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 141. -/
private theorem cell141 {x : ℝ} (ha : 141 ≤ x) (hb : x < 151) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (141402 : ℝ) / 1000 ≤ Chebyshev.psi 141 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 141) (k := 204) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 150 ≤ (146948 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 150) (k := 211) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨141, 151, 141402, 146948, 9618, 9953⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 151. -/
private theorem cell151 {x : ℝ} (ha : 151 ≤ x) (hb : x < 161) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (151106 : ℝ) / 1000 ≤ Chebyshev.psi 151 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 151) (k := 218) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 160 ≤ (157345 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 160) (k := 226) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨151, 161, 151106, 157345, 9953, 10277⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 161. -/
private theorem cell161 {x : ℝ} (ha : 161 ≤ x) (hb : x < 167) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (156651 : ℝ) / 1000 ≤ Chebyshev.psi 161 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 161) (k := 226) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 166 ≤ (162197 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 166) (k := 233) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨161, 167, 156651, 162197, 10277, 10467⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 167. -/
private theorem cell167 {x : ℝ} (ha : 167 ≤ x) (hb : x < 177) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (166355 : ℝ) / 1000 ≤ Chebyshev.psi 167 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 167) (k := 240) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 176 ≤ (174674 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 176) (k := 251) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨167, 177, 166355, 174674, 10467, 10776⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 177. -/
private theorem cell177 {x : ℝ} (ha : 177 ≤ x) (hb : x < 184) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (173979 : ℝ) / 1000 ≤ Chebyshev.psi 177 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 177) (k := 251) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 183 ≤ (185071 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 183) (k := 266) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨177, 184, 173979, 185071, 10776, 10987⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 184. -/
private theorem cell184 {x : ℝ} (ha : 184 ≤ x) (hb : x < 193) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (184377 : ℝ) / 1000 ≤ Chebyshev.psi 184 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 184) (k := 266) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 192 ≤ (190616 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 192) (k := 274) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact Arithmetic.psi81_cell_sound ⟨184, 193, 184377, 190616, 10987, 11252⟩ (by decide) hl hu ha hb

/-- The checked cells cover every real point in the half-open interval [88, 193). -/
theorem psi81_on_88_193 {x : ℝ} (ha : 88 ≤ x) (hb : x < 193) :
    |Chebyshev.psi x - x| / Real.sqrt x ≤ (81 / 100 : ℝ) := by
  have hx : 0 < x := by linarith only [ha]
  apply (div_le_iff₀ (Real.sqrt_pos.2 hx)).2
  by_cases h92 : x < 92
  · exact cell88 ha h92
  by_cases h97 : x < 97
  · exact cell92 (le_of_not_gt h92) h97
  by_cases h101 : x < 101
  · exact cell97 (le_of_not_gt h97) h101
  by_cases h106 : x < 106
  · exact cell101 (le_of_not_gt h101) h106
  by_cases h111 : x < 111
  · exact cell106 (le_of_not_gt h106) h111
  by_cases h121 : x < 121
  · exact cell111 (le_of_not_gt h111) h121
  by_cases h128 : x < 128
  · exact cell121 (le_of_not_gt h121) h128
  by_cases h136 : x < 136
  · exact cell128 (le_of_not_gt h128) h136
  by_cases h141 : x < 141
  · exact cell136 (le_of_not_gt h136) h141
  by_cases h151 : x < 151
  · exact cell141 (le_of_not_gt h141) h151
  by_cases h161 : x < 161
  · exact cell151 (le_of_not_gt h151) h161
  by_cases h167 : x < 167
  · exact cell161 (le_of_not_gt h161) h167
  by_cases h177 : x < 177
  · exact cell167 (le_of_not_gt h167) h177
  by_cases h184 : x < 184
  · exact cell177 (le_of_not_gt h177) h184
  exact cell184 (le_of_not_gt h184) hb

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound
