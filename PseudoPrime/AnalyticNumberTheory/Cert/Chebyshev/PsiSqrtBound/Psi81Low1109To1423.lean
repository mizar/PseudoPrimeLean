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

/-! # Chebyshev psi certificate on [1109, 1423) -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound

/-- LCM comparisons and the integer crossing check certify the cell starting at 1109. -/
private theorem cell1109 {x : ℝ} (ha : 1109 ≤ x) (hb : x < 1123) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (1122205 : ℝ) / 1000 ≤ Chebyshev.psi 1109 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 1109) (k := 1619) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 1122 ≤ (1129830 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 1122) (k := 1629) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact
    Arithmetic.psi81_cell_sound ⟨1109, 1123, 1122205, 1129830, 26974, 27144⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 1123. -/
private theorem cell1123 {x : ℝ} (ha : 1123 ≤ x) (hb : x < 1151) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (1136068 : ℝ) / 1000 ≤ Chebyshev.psi 1123 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 1123) (k := 1639) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 1150 ≤ (1144386 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 1150) (k := 1650) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact
    Arithmetic.psi81_cell_sound ⟨1123, 1151, 1136068, 1144386, 27144, 27480⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 1151. -/
private theorem cell1151 {x : ℝ} (ha : 1151 ≤ x) (hb : x < 1178) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (1150624 : ℝ) / 1000 ≤ Chebyshev.psi 1151 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 1151) (k := 1660) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 1177 ≤ (1172112 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 1177) (k := 1690) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact
    Arithmetic.psi81_cell_sound ⟨1151, 1178, 1150624, 1172112, 27480, 27800⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 1178. -/
private theorem cell1178 {x : ℝ} (ha : 1178 ≤ x) (hb : x < 1199) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (1171418 : ℝ) / 1000 ≤ Chebyshev.psi 1178 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 1178) (k := 1690) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 1198 ≤ (1193600 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 1198) (k := 1721) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact
    Arithmetic.psi81_cell_sound ⟨1178, 1199, 1171418, 1193600, 27800, 28047⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 1199. -/
private theorem cell1199 {x : ℝ} (ha : 1199 ≤ x) (hb : x < 1221) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (1192906 : ℝ) / 1000 ≤ Chebyshev.psi 1199 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 1199) (k := 1721) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 1220 ≤ (1215088 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 1220) (k := 1752) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact
    Arithmetic.psi81_cell_sound ⟨1199, 1221, 1192906, 1215088, 28047, 28303⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 1221. -/
private theorem cell1221 {x : ℝ} (ha : 1221 ≤ x) (hb : x < 1242) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (1214393 : ℝ) / 1000 ≤ Chebyshev.psi 1221 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 1221) (k := 1752) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 1241 ≤ (1243507 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 1241) (k := 1793) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact
    Arithmetic.psi81_cell_sound ⟨1221, 1242, 1214393, 1243507, 28303, 28546⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 1242. -/
private theorem cell1242 {x : ℝ} (ha : 1242 ≤ x) (hb : x < 1271) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (1242812 : ℝ) / 1000 ≤ Chebyshev.psi 1242 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 1242) (k := 1793) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 1270 ≤ (1257369 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 1270) (k := 1813) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact
    Arithmetic.psi81_cell_sound ⟨1242, 1271, 1242812, 1257369, 28546, 28877⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 1271. -/
private theorem cell1271 {x : ℝ} (ha : 1271 ≤ x) (hb : x < 1285) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (1256675 : ℝ) / 1000 ≤ Chebyshev.psi 1271 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 1271) (k := 1813) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 1284 ≤ (1278857 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 1284) (k := 1844) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact
    Arithmetic.psi81_cell_sound ⟨1271, 1285, 1256675, 1278857, 28877, 29035⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 1285. -/
private theorem cell1285 {x : ℝ} (ha : 1285 ≤ x) (hb : x < 1303) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (1278163 : ℝ) / 1000 ≤ Chebyshev.psi 1285 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 1285) (k := 1844) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 1302 ≤ (1307969 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 1302) (k := 1886) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact
    Arithmetic.psi81_cell_sound ⟨1285, 1303, 1278163, 1307969, 29035, 29238⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 1303. -/
private theorem cell1303 {x : ℝ} (ha : 1303 ≤ x) (hb : x < 1321) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (1314207 : ℝ) / 1000 ≤ Chebyshev.psi 1303 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 1303) (k := 1896) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 1320 ≤ (1329457 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 1320) (k := 1917) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact
    Arithmetic.psi81_cell_sound ⟨1303, 1321, 1314207, 1329457, 29238, 29439⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 1321. -/
private theorem cell1321 {x : ℝ} (ha : 1321 ≤ x) (hb : x < 1361) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (1335694 : ℝ) / 1000 ≤ Chebyshev.psi 1321 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 1321) (k := 1927) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 1360 ≤ (1346092 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 1360) (k := 1941) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact
    Arithmetic.psi81_cell_sound ⟨1321, 1361, 1335694, 1346092, 29439, 29882⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 1361. -/
private theorem cell1361 {x : ℝ} (ha : 1361 ≤ x) (hb : x < 1382) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (1352330 : ℝ) / 1000 ≤ Chebyshev.psi 1361 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 1361) (k := 1951) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 1381 ≤ (1378670 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 1381) (k := 1988) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact
    Arithmetic.psi81_cell_sound ⟨1361, 1382, 1352330, 1378670, 29882, 30111⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 1382. -/
private theorem cell1382 {x : ℝ} (ha : 1382 ≤ x) (hb : x < 1408) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (1377976 : ℝ) / 1000 ≤ Chebyshev.psi 1382 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 1382) (k := 1988) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 1407 ≤ (1385602 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 1407) (k := 1998) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact
    Arithmetic.psi81_cell_sound ⟨1382, 1408, 1377976, 1385602, 30111, 30393⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 1408. -/
private theorem cell1408 {x : ℝ} (ha : 1408 ≤ x) (hb : x < 1415) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (1384908 : ℝ) / 1000 ≤ Chebyshev.psi 1408 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 1408) (k := 1998) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 1414 ≤ (1393226 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 1414) (k := 2009) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact
    Arithmetic.psi81_cell_sound ⟨1408, 1415, 1384908, 1393226, 30393, 30469⟩ (by decide) hl hu ha hb

/-- LCM comparisons and the integer crossing check certify the cell starting at 1415. -/
private theorem cell1415 {x : ℝ} (ha : 1415 ≤ x) (hb : x < 1423) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hl : (1392532 : ℝ) / 1000 ≤ Chebyshev.psi 1415 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 1415) (k := 2009) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h.1, Real.log_two_gt_d9]
  have hu : Chebyshev.psi 1422 ≤ (1393226 : ℝ) / 1000 := by
    have h :=
      Arithmetic.psi_bounds_of_lcm_pow_two (n := 1422) (k := 2009) (by decide +kernel)
        (by decide +kernel)
    norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
    linarith only [h.2, Real.log_two_lt_d9]
  exact
    Arithmetic.psi81_cell_sound ⟨1415, 1423, 1392532, 1393226, 30469, 30555⟩ (by decide) hl hu ha hb

/-- The checked cells cover every real point in the half-open interval [1109, 1423). -/
theorem psi81_on_1109_1423 {x : ℝ} (ha : 1109 ≤ x) (hb : x < 1423) :
    |Chebyshev.psi x - x| / Real.sqrt x ≤ (81 / 100 : ℝ) := by
  have hx : 0 < x := by linarith only [ha]
  apply (div_le_iff₀ (Real.sqrt_pos.2 hx)).2
  by_cases h1123 : x < 1123
  · exact cell1109 ha h1123
  by_cases h1151 : x < 1151
  · exact cell1123 (le_of_not_gt h1123) h1151
  by_cases h1178 : x < 1178
  · exact cell1151 (le_of_not_gt h1151) h1178
  by_cases h1199 : x < 1199
  · exact cell1178 (le_of_not_gt h1178) h1199
  by_cases h1221 : x < 1221
  · exact cell1199 (le_of_not_gt h1199) h1221
  by_cases h1242 : x < 1242
  · exact cell1221 (le_of_not_gt h1221) h1242
  by_cases h1271 : x < 1271
  · exact cell1242 (le_of_not_gt h1242) h1271
  by_cases h1285 : x < 1285
  · exact cell1271 (le_of_not_gt h1271) h1285
  by_cases h1303 : x < 1303
  · exact cell1285 (le_of_not_gt h1285) h1303
  by_cases h1321 : x < 1321
  · exact cell1303 (le_of_not_gt h1303) h1321
  by_cases h1361 : x < 1361
  · exact cell1321 (le_of_not_gt h1321) h1361
  by_cases h1382 : x < 1382
  · exact cell1361 (le_of_not_gt h1361) h1382
  by_cases h1408 : x < 1408
  · exact cell1382 (le_of_not_gt h1382) h1408
  by_cases h1415 : x < 1415
  · exact cell1408 (le_of_not_gt h1408) h1415
  exact cell1415 (le_of_not_gt h1415) hb

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound
