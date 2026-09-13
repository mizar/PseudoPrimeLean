/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-! # General bounds and arithmetic certificates -/

namespace PseudoPrime.Analysis

/-- Split a harmonic number into a fixed-size tail, so numeric reduction stays shallow. -/
private theorem harmonic_add_block (n k : ℕ) :
    harmonic (n + k) = harmonic n + ∑ i ∈ Finset.range k, ((n + i + 1 : ℕ) : ℚ)⁻¹ := by
  induction k with
  | zero => simp only [add_zero, Finset.range_zero, Nat.cast_add, Nat.cast_one, Finset.sum_empty]
  | succ k ih =>
    rw [Nat.add_succ, harmonic_succ, ih, Finset.sum_range_succ]
    simp only [add_assoc]

-- BEGIN GENERATED harmonic_blocks
/-- Exact harmonic value at 32, computed from the preceding 32-term block. -/
private theorem harmonic_block_32 : harmonic 32 =
    (586061125622639 /
      144403552893600 : ℚ) := by
  norm_num [harmonic, Finset.sum_range_succ]

/-- Exact harmonic value at 64, computed from the preceding 32-term block. -/
private theorem harmonic_block_64 : harmonic 64 =
    (623171679694215690971693339 /
      131362987122535807501262400 : ℚ) := by
  rw [show 64 = 32 + 32 by rfl, harmonic_add_block, harmonic_block_32]
  norm_num [Finset.sum_range_succ]

/-- Exact harmonic value at 96, computed from the preceding 32-term block. -/
private theorem harmonic_block_96 : harmonic 96 =
    (3699322246041458103739317199996707235031 /
      718766754945489455304472257065075294400 : ℚ) := by
  rw [show 96 = 64 + 32 by rfl, harmonic_add_block, harmonic_block_64]
  norm_num [Finset.sum_range_succ]

/-- Exact harmonic value at 128, computed from the preceding 32-term block. -/
private theorem harmonic_block_128 : harmonic 128 =
    (72552921080947538317446905633815133414572988188576608701 /
      13353756090997411579403749204440236542538872688049072000 : ℚ) := by
  rw [show 128 = 96 + 32 by rfl, harmonic_add_block, harmonic_block_96]
  norm_num [Finset.sum_range_succ]

/-- Exact harmonic value at 160, computed from the preceding 32-term block. -/
private theorem harmonic_block_160 : harmonic 160 =
    ((51191928 * 10 ^ 60 +
        86341439450197272044235040542874227018635634639310431809803) /
      (9051688 * 10 ^ 60 +
        883684759602914678126258667842076023307933940069074670736000) : ℚ) := by
  rw [show 160 = 128 + 32 by rfl, harmonic_add_block, harmonic_block_128]
  norm_num [Finset.sum_range_succ]

/-- Exact harmonic value at 192, computed from the preceding 32-term block. -/
private theorem harmonic_block_192 : harmonic 192 =
    ((28913584925453013418184 * 10 ^ 60 +
        554684785072907056401554990076275925448503973084282785831921) /
      (4953235368325372168838 * 10 ^ 60 +
        690158677648217774187866309874717606205514731838121853072000) : ℚ) := by
  rw [show 192 = 160 + 32 by rfl, harmonic_add_block, harmonic_block_160]
  norm_num [Finset.sum_range_succ]

/-- Exact harmonic value at 224, computed from the preceding 32-term block. -/
private theorem harmonic_block_224 : harmonic 224 =
    ((31694226197390460594676973029075117 * 10 ^ 60 +
        447594166556283276266818239502270534182120445732476389857641) /
      (5290225078451893176693594241665890 * 10 ^ 60 +
        914638817631063334447389979640757204083936351078274058192000) : ℚ) := by
  rw [show 224 = 192 + 32 by rfl, harmonic_add_block, harmonic_block_192]
  norm_num [Finset.sum_range_succ]

/-- Exact harmonic value at 256, computed from the preceding 32-term block. -/
private theorem harmonic_block_256 : harmonic 256 =
    ((102120333780755602922415011407986918913493325085710 * 10 ^ 60 +
        168750386125102325162741298648605491283438121466698312402217) /
      (16674490806895842671659008751776385350270324508909 * 10 ^ 60 +
        651849955453691538889375930032935391666564679008085339616000) : ℚ) := by
  rw [show 256 = 224 + 32 by rfl, harmonic_add_block, harmonic_block_224]
  norm_num [Finset.sum_range_succ]

-- END GENERATED harmonic_blocks

/-- A kernel-checked rational upper bound for the Euler--Mascheroni constant. -/
theorem eulerMascheroniConstant_lt_twentyNine_fiftieths :
    Real.eulerMascheroniConstant < (29 / 50 : ℝ) := by
  have hγ := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 256
  rw [Real.eulerMascheroniSeq'] at hγ
  rw [ite_eq_right (by decide), harmonic_block_256] at hγ
  norm_num only at hγ
  have hlog : Real.log (256 : ℝ) = 8 * Real.log 2 := by
    rw [show (256 : ℝ) = 2 ^ 8 by norm_num only, Real.log_pow]
    norm_num only
  rw [hlog] at hγ
  nlinarith [Real.log_two_gt_d9]

/-- A coarse logarithmic lower bound sufficient for the reciprocal remainder estimate. -/
theorem three_halves_le_log_two_pi : (3 / 2 : ℝ) ≤ Real.log (2 * Real.pi) := by
  have hlogSix : (3 / 2 : ℝ) < Real.log 6 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num only, Real.log_mul (by norm_num only) (by norm_num only)]
    linarith [Real.log_two_gt_d9, Real.log_three_gt_d9]
  have hsix : (6 : ℝ) < 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  exact
    hlogSix.le.trans
      (Real.strictMonoOn_log (by norm_num only [Set.mem_Ioi])
          (show (0 : ℝ) < 2 * Real.pi by positivity) hsix).le

/-- The closed geometric tail is at most `1 / (18x)` on `x ≥ 2`. -/
theorem geometricTail_le_one_div_eighteen_mul {x : ℝ} (hx : 2 ≤ x) :
    x⁻¹ ^ 3 / 6 * (1 - x⁻¹ ^ 2)⁻¹ ≤ 1 / (18 * x) := by
  have hxpos : 0 < x := by linarith
  have hxsq : 0 < x ^ 2 - 1 := by nlinarith
  field_simp [hxpos.ne', hxsq.ne']
  nlinarith

/-- Square completion balances the zero-mass term against `1/50 + 9/(8x)`. -/
theorem three_tenths_div_sqrt_le {x : ℝ} (hx : 2 ≤ x) :
    3 / (10 * Real.sqrt x) ≤ 1 / 50 + 9 / (8 * x) := by
  have hxpos : 0 < x := by linarith
  have hsqrt : 0 < Real.sqrt x := Real.sqrt_pos.2 hxpos
  have hsquare : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hxpos.le
  field_simp [hxpos.ne', hsqrt.ne']
  nlinarith [sq_nonneg (2 * Real.sqrt x - 15)]

end PseudoPrime.Analysis
