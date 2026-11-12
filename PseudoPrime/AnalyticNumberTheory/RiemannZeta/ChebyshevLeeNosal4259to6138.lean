/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevLcmBounds
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevIntervalPrefix
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalLogCheck
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalMonotone
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalChecker

/-! # Batch certificate for Lee–Nosal psi cells -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The local cells store endpoint bounds in thousandths. -/
private def batchCells : List LeeNosalCell :=
  [⟨4259, 4397, 4273252, 4391088, 133000, 133000⟩, ⟨4397, 4523, 4398712, 4529717, 133000, 133000⟩,
    ⟨4523, 4657, 4537341, 4655870, 133000, 133000⟩, ⟨4657, 4793, 4664187, 4782716, 133000, 133000⟩,
    ⟨4793, 4924, 4791033, 4896392, 133000, 133000⟩, ⟨4924, 5028, 4895698, 5040567, 133000, 133000⟩,
    ⟨5028, 5167, 5039873, 5156322, 133000, 133000⟩, ⟨5167, 5296, 5163946, 5276237, 133000, 133000⟩,
    ⟨5296, 5408, 5275543, 5382982, 133000, 133000⟩, ⟨5408, 5515, 5382287, 5512600, 133000, 133000⟩,
    ⟨5515, 5644, 5511906, 5624197, 133000, 133000⟩, ⟨5644, 5756, 5623503, 5762826, 133000, 133000⟩,
    ⟨5756, 5867, 5762132, 5884127, 133000, 133000⟩, ⟨5867, 6011, 5892444, 5997110, 133000, 133000⟩,
    ⟨6011, 6138, 6005427, 6136432, 133000, 133000⟩]

/-- The kernel-checked prefix bounds for 4259. -/
private theorem psi_4259_bounds :
    (4273252 : ℝ) / 1000 ≤ Chebyshev.psi 4259 ∧ Chebyshev.psi 4259 ≤ (4273946 : ℝ) / 1000 := by
  have hl : 2 ^ 6165 ≤ Nat.lcmUpto 4259 := by decide +kernel
  have hu : Nat.lcmUpto 4259 ≤ 2 ^ (6165 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 4391. -/
private theorem psi_4391_bounds :
    (4390394 : ℝ) / 1000 ≤ Chebyshev.psi 4391 ∧ Chebyshev.psi 4391 ≤ (4391088 : ℝ) / 1000 := by
  have hl : 2 ^ 6334 ≤ Nat.lcmUpto 4391 := by decide +kernel
  have hu : Nat.lcmUpto 4391 ≤ 2 ^ (6334 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 4397. -/
private theorem psi_4397_bounds :
    (4398712 : ℝ) / 1000 ≤ Chebyshev.psi 4397 ∧ Chebyshev.psi 4397 ≤ (4399406 : ℝ) / 1000 := by
  have hl : 2 ^ 6346 ≤ Nat.lcmUpto 4397 := by decide +kernel
  have hu : Nat.lcmUpto 4397 ≤ 2 ^ (6346 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 4519. -/
private theorem psi_4519_bounds :
    (4529023 : ℝ) / 1000 ≤ Chebyshev.psi 4519 ∧ Chebyshev.psi 4519 ≤ (4529717 : ℝ) / 1000 := by
  have hl : 2 ^ 6534 ≤ Nat.lcmUpto 4519 := by decide +kernel
  have hu : Nat.lcmUpto 4519 ≤ 2 ^ (6534 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 4523. -/
private theorem psi_4523_bounds :
    (4537341 : ℝ) / 1000 ≤ Chebyshev.psi 4523 ∧ Chebyshev.psi 4523 ≤ (4538035 : ℝ) / 1000 := by
  have hl : 2 ^ 6546 ≤ Nat.lcmUpto 4523 := by decide +kernel
  have hu : Nat.lcmUpto 4523 ≤ 2 ^ (6546 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 4651. -/
private theorem psi_4651_bounds :
    (4655176 : ℝ) / 1000 ≤ Chebyshev.psi 4651 ∧ Chebyshev.psi 4651 ≤ (4655870 : ℝ) / 1000 := by
  have hl : 2 ^ 6716 ≤ Nat.lcmUpto 4651 := by decide +kernel
  have hu : Nat.lcmUpto 4651 ≤ 2 ^ (6716 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 4657. -/
private theorem psi_4657_bounds :
    (4664187 : ℝ) / 1000 ≤ Chebyshev.psi 4657 ∧ Chebyshev.psi 4657 ≤ (4664881 : ℝ) / 1000 := by
  have hl : 2 ^ 6729 ≤ Nat.lcmUpto 4657 := by decide +kernel
  have hu : Nat.lcmUpto 4657 ≤ 2 ^ (6729 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 4789. -/
private theorem psi_4789_bounds :
    (4782022 : ℝ) / 1000 ≤ Chebyshev.psi 4789 ∧ Chebyshev.psi 4789 ≤ (4782716 : ℝ) / 1000 := by
  have hl : 2 ^ 6899 ≤ Nat.lcmUpto 4789 := by decide +kernel
  have hu : Nat.lcmUpto 4789 ≤ 2 ^ (6899 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 4793. -/
private theorem psi_4793_bounds :
    (4791033 : ℝ) / 1000 ≤ Chebyshev.psi 4793 ∧ Chebyshev.psi 4793 ≤ (4791727 : ℝ) / 1000 := by
  have hl : 2 ^ 6912 ≤ Nat.lcmUpto 4793 := by decide +kernel
  have hu : Nat.lcmUpto 4793 ≤ 2 ^ (6912 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 4919. -/
private theorem psi_4919_bounds :
    (4895698 : ℝ) / 1000 ≤ Chebyshev.psi 4919 ∧ Chebyshev.psi 4919 ≤ (4896392 : ℝ) / 1000 := by
  have hl : 2 ^ 7063 ≤ Nat.lcmUpto 4919 := by decide +kernel
  have hu : Nat.lcmUpto 4919 ≤ 2 ^ (7063 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 5023. -/
private theorem psi_5023_bounds :
    (5039873 : ℝ) / 1000 ≤ Chebyshev.psi 5023 ∧ Chebyshev.psi 5023 ≤ (5040567 : ℝ) / 1000 := by
  have hl : 2 ^ 7271 ≤ Nat.lcmUpto 5023 := by decide +kernel
  have hu : Nat.lcmUpto 5023 ≤ 2 ^ (7271 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 5153. -/
private theorem psi_5153_bounds :
    (5155628 : ℝ) / 1000 ≤ Chebyshev.psi 5153 ∧ Chebyshev.psi 5153 ≤ (5156322 : ℝ) / 1000 := by
  have hl : 2 ^ 7438 ≤ Nat.lcmUpto 5153 := by decide +kernel
  have hu : Nat.lcmUpto 5153 ≤ 2 ^ (7438 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 5167. -/
private theorem psi_5167_bounds :
    (5163946 : ℝ) / 1000 ≤ Chebyshev.psi 5167 ∧ Chebyshev.psi 5167 ≤ (5164640 : ℝ) / 1000 := by
  have hl : 2 ^ 7450 ≤ Nat.lcmUpto 5167 := by decide +kernel
  have hu : Nat.lcmUpto 5167 ≤ 2 ^ (7450 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 5281. -/
private theorem psi_5281_bounds :
    (5275543 : ℝ) / 1000 ≤ Chebyshev.psi 5281 ∧ Chebyshev.psi 5281 ≤ (5276237 : ℝ) / 1000 := by
  have hl : 2 ^ 7611 ≤ Nat.lcmUpto 5281 := by decide +kernel
  have hu : Nat.lcmUpto 5281 ≤ 2 ^ (7611 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 5407. -/
private theorem psi_5407_bounds :
    (5382287 : ℝ) / 1000 ≤ Chebyshev.psi 5407 ∧ Chebyshev.psi 5407 ≤ (5382982 : ℝ) / 1000 := by
  have hl : 2 ^ 7765 ≤ Nat.lcmUpto 5407 := by decide +kernel
  have hu : Nat.lcmUpto 5407 ≤ 2 ^ (7765 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 5507. -/
private theorem psi_5507_bounds :
    (5511906 : ℝ) / 1000 ≤ Chebyshev.psi 5507 ∧ Chebyshev.psi 5507 ≤ (5512600 : ℝ) / 1000 := by
  have hl : 2 ^ 7952 ≤ Nat.lcmUpto 5507 := by decide +kernel
  have hu : Nat.lcmUpto 5507 ≤ 2 ^ (7952 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 5641. -/
private theorem psi_5641_bounds :
    (5623503 : ℝ) / 1000 ≤ Chebyshev.psi 5641 ∧ Chebyshev.psi 5641 ≤ (5624197 : ℝ) / 1000 := by
  have hl : 2 ^ 8113 ≤ Nat.lcmUpto 5641 := by decide +kernel
  have hu : Nat.lcmUpto 5641 ≤ 2 ^ (8113 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 5749. -/
private theorem psi_5749_bounds :
    (5762132 : ℝ) / 1000 ≤ Chebyshev.psi 5749 ∧ Chebyshev.psi 5749 ≤ (5762826 : ℝ) / 1000 := by
  have hl : 2 ^ 8313 ≤ Nat.lcmUpto 5749 := by decide +kernel
  have hu : Nat.lcmUpto 5749 ≤ 2 ^ (8313 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 5861. -/
private theorem psi_5861_bounds :
    (5883433 : ℝ) / 1000 ≤ Chebyshev.psi 5861 ∧ Chebyshev.psi 5861 ≤ (5884127 : ℝ) / 1000 := by
  have hl : 2 ^ 8488 ≤ Nat.lcmUpto 5861 := by decide +kernel
  have hu : Nat.lcmUpto 5861 ≤ 2 ^ (8488 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 5867. -/
private theorem psi_5867_bounds :
    (5892444 : ℝ) / 1000 ≤ Chebyshev.psi 5867 ∧ Chebyshev.psi 5867 ≤ (5893138 : ℝ) / 1000 := by
  have hl : 2 ^ 8501 ≤ Nat.lcmUpto 5867 := by decide +kernel
  have hu : Nat.lcmUpto 5867 ≤ 2 ^ (8501 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 6007. -/
private theorem psi_6007_bounds :
    (5996416 : ℝ) / 1000 ≤ Chebyshev.psi 6007 ∧ Chebyshev.psi 6007 ≤ (5997110 : ℝ) / 1000 := by
  have hl : 2 ^ 8651 ≤ Nat.lcmUpto 6007 := by decide +kernel
  have hu : Nat.lcmUpto 6007 ≤ 2 ^ (8651 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 6011. -/
private theorem psi_6011_bounds :
    (6005427 : ℝ) / 1000 ≤ Chebyshev.psi 6011 ∧ Chebyshev.psi 6011 ≤ (6006121 : ℝ) / 1000 := by
  have hl : 2 ^ 8664 ≤ Nat.lcmUpto 6011 := by decide +kernel
  have hu : Nat.lcmUpto 6011 ≤ 2 ^ (8664 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 6133. -/
private theorem psi_6133_bounds :
    (6135738 : ℝ) / 1000 ≤ Chebyshev.psi 6133 ∧ Chebyshev.psi 6133 ≤ (6136432 : ℝ) / 1000 := by
  have hl : 2 ^ 8852 ≤ Nat.lcmUpto 6133 := by decide +kernel
  have hu : Nat.lcmUpto 6133 ≤ 2 ^ (8852 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- A rational certificate bounds the envelope from 4259 onward. -/
private theorem batch_envelope {t : ℝ} (ht : 4259 ≤ t) :
    (133 : ℝ) ≤
      Real.sqrt t * (Real.log t * (Real.log t - Real.log (Real.log t)) / (8 * Real.pi)) := by
  have h :=
    lee_nosal_envelope_of_log_checks (N := 4259) (lo := 835 / 100) (hi := 836 / 100) (vlo :=
      212 / 100) (vhi := 213 / 100) (c := 133) (j := 13) (k := 4) (n := 32) (m := 32)
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by decide +kernel) (by decide +kernel) (by norm_num only)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact
    h.trans
      (lee_nosal_envelope_mono (x := 4259) (y := t)
        (Real.exp_one_lt_three.le.trans (by norm_num only)) ht)

/-- Every batch cell has a checked psi lower bound. -/
private theorem batch_lower : ∀ r ∈ batchCells, (r.lo : ℝ) / 1000 ≤ Chebyshev.psi r.a := by
  intro r hr
  simp only [batchCells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl
  · change (4273252 : ℝ) / 1000 ≤ Chebyshev.psi (↑(4259 : ℕ) : ℝ)
    exact psi_4259_bounds.1
  · change (4398712 : ℝ) / 1000 ≤ Chebyshev.psi (↑(4397 : ℕ) : ℝ)
    exact psi_4397_bounds.1
  · change (4537341 : ℝ) / 1000 ≤ Chebyshev.psi (↑(4523 : ℕ) : ℝ)
    exact psi_4523_bounds.1
  · change (4664187 : ℝ) / 1000 ≤ Chebyshev.psi (↑(4657 : ℕ) : ℝ)
    exact psi_4657_bounds.1
  · change (4791033 : ℝ) / 1000 ≤ Chebyshev.psi (↑(4793 : ℕ) : ℝ)
    exact psi_4793_bounds.1
  · change (4895698 : ℝ) / 1000 ≤ Chebyshev.psi (↑(4924 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 4919) (b := 4924) (by decide) (by decide +kernel)]
    exact psi_4919_bounds.1
  · change (5039873 : ℝ) / 1000 ≤ Chebyshev.psi (↑(5028 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 5023) (b := 5028) (by decide) (by decide +kernel)]
    exact psi_5023_bounds.1
  · change (5163946 : ℝ) / 1000 ≤ Chebyshev.psi (↑(5167 : ℕ) : ℝ)
    exact psi_5167_bounds.1
  · change (5275543 : ℝ) / 1000 ≤ Chebyshev.psi (↑(5296 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 5281) (b := 5296) (by decide) (by decide +kernel)]
    exact psi_5281_bounds.1
  · change (5382287 : ℝ) / 1000 ≤ Chebyshev.psi (↑(5408 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 5407) (b := 5408) (by decide) (by decide +kernel)]
    exact psi_5407_bounds.1
  · change (5511906 : ℝ) / 1000 ≤ Chebyshev.psi (↑(5515 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 5507) (b := 5515) (by decide) (by decide +kernel)]
    exact psi_5507_bounds.1
  · change (5623503 : ℝ) / 1000 ≤ Chebyshev.psi (↑(5644 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 5641) (b := 5644) (by decide) (by decide +kernel)]
    exact psi_5641_bounds.1
  · change (5762132 : ℝ) / 1000 ≤ Chebyshev.psi (↑(5756 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 5749) (b := 5756) (by decide) (by decide +kernel)]
    exact psi_5749_bounds.1
  · change (5892444 : ℝ) / 1000 ≤ Chebyshev.psi (↑(5867 : ℕ) : ℝ)
    exact psi_5867_bounds.1
  · change (6005427 : ℝ) / 1000 ≤ Chebyshev.psi (↑(6011 : ℕ) : ℝ)
    exact psi_6011_bounds.1

/-- Every batch cell has a checked psi upper bound. -/
private theorem batch_upper :
    ∀ r ∈ batchCells, Chebyshev.psi (r.b - 1 : ℕ) ≤ (r.hi : ℝ) / 1000 := by
  intro r hr
  simp only [batchCells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl
  · change Chebyshev.psi (↑(4396 : ℕ) : ℝ) ≤ (4391088 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 4391) (b := 4396) (by decide) (by decide +kernel)]
    exact psi_4391_bounds.2
  · change Chebyshev.psi (↑(4522 : ℕ) : ℝ) ≤ (4529717 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 4519) (b := 4522) (by decide) (by decide +kernel)]
    exact psi_4519_bounds.2
  · change Chebyshev.psi (↑(4656 : ℕ) : ℝ) ≤ (4655870 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 4651) (b := 4656) (by decide) (by decide +kernel)]
    exact psi_4651_bounds.2
  · change Chebyshev.psi (↑(4792 : ℕ) : ℝ) ≤ (4782716 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 4789) (b := 4792) (by decide) (by decide +kernel)]
    exact psi_4789_bounds.2
  · change Chebyshev.psi (↑(4923 : ℕ) : ℝ) ≤ (4896392 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 4919) (b := 4923) (by decide) (by decide +kernel)]
    exact psi_4919_bounds.2
  · change Chebyshev.psi (↑(5027 : ℕ) : ℝ) ≤ (5040567 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 5023) (b := 5027) (by decide) (by decide +kernel)]
    exact psi_5023_bounds.2
  · change Chebyshev.psi (↑(5166 : ℕ) : ℝ) ≤ (5156322 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 5153) (b := 5166) (by decide) (by decide +kernel)]
    exact psi_5153_bounds.2
  · change Chebyshev.psi (↑(5295 : ℕ) : ℝ) ≤ (5276237 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 5281) (b := 5295) (by decide) (by decide +kernel)]
    exact psi_5281_bounds.2
  · change Chebyshev.psi (↑(5407 : ℕ) : ℝ) ≤ (5382982 : ℝ) / 1000
    exact psi_5407_bounds.2
  · change Chebyshev.psi (↑(5514 : ℕ) : ℝ) ≤ (5512600 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 5507) (b := 5514) (by decide) (by decide +kernel)]
    exact psi_5507_bounds.2
  · change Chebyshev.psi (↑(5643 : ℕ) : ℝ) ≤ (5624197 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 5641) (b := 5643) (by decide) (by decide +kernel)]
    exact psi_5641_bounds.2
  · change Chebyshev.psi (↑(5755 : ℕ) : ℝ) ≤ (5762826 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 5749) (b := 5755) (by decide) (by decide +kernel)]
    exact psi_5749_bounds.2
  · change Chebyshev.psi (↑(5866 : ℕ) : ℝ) ≤ (5884127 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 5861) (b := 5866) (by decide) (by decide +kernel)]
    exact psi_5861_bounds.2
  · change Chebyshev.psi (↑(6010 : ℕ) : ℝ) ≤ (5997110 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 6007) (b := 6010) (by decide) (by decide +kernel)]
    exact psi_6007_bounds.2
  · change Chebyshev.psi (↑(6137 : ℕ) : ℝ) ≤ (6136432 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 6133) (b := 6137) (by decide) (by decide +kernel)]
    exact psi_6133_bounds.2

/-- The envelope bound applies at every cell a endpoint. -/
private theorem batch_a :
    ∀ r ∈ batchCells,
      (r.ca : ℝ) / 1000 ≤
        Real.sqrt r.a *
          (Real.log r.a * (Real.log r.a - Real.log (Real.log r.a)) / (8 * Real.pi)) := by
  intro r hr
  simp only [batchCells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl
  · change
      (133000 : ℝ) / 1000 ≤
        Real.sqrt 4259 *
          (Real.log 4259 * (Real.log 4259 - Real.log (Real.log 4259)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (133000 : ℝ) / 1000 ≤
        Real.sqrt 4397 *
          (Real.log 4397 * (Real.log 4397 - Real.log (Real.log 4397)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (133000 : ℝ) / 1000 ≤
        Real.sqrt 4523 *
          (Real.log 4523 * (Real.log 4523 - Real.log (Real.log 4523)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (133000 : ℝ) / 1000 ≤
        Real.sqrt 4657 *
          (Real.log 4657 * (Real.log 4657 - Real.log (Real.log 4657)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (133000 : ℝ) / 1000 ≤
        Real.sqrt 4793 *
          (Real.log 4793 * (Real.log 4793 - Real.log (Real.log 4793)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (133000 : ℝ) / 1000 ≤
        Real.sqrt 4924 *
          (Real.log 4924 * (Real.log 4924 - Real.log (Real.log 4924)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (133000 : ℝ) / 1000 ≤
        Real.sqrt 5028 *
          (Real.log 5028 * (Real.log 5028 - Real.log (Real.log 5028)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (133000 : ℝ) / 1000 ≤
        Real.sqrt 5167 *
          (Real.log 5167 * (Real.log 5167 - Real.log (Real.log 5167)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (133000 : ℝ) / 1000 ≤
        Real.sqrt 5296 *
          (Real.log 5296 * (Real.log 5296 - Real.log (Real.log 5296)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (133000 : ℝ) / 1000 ≤
        Real.sqrt 5408 *
          (Real.log 5408 * (Real.log 5408 - Real.log (Real.log 5408)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (133000 : ℝ) / 1000 ≤
        Real.sqrt 5515 *
          (Real.log 5515 * (Real.log 5515 - Real.log (Real.log 5515)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (133000 : ℝ) / 1000 ≤
        Real.sqrt 5644 *
          (Real.log 5644 * (Real.log 5644 - Real.log (Real.log 5644)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (133000 : ℝ) / 1000 ≤
        Real.sqrt 5756 *
          (Real.log 5756 * (Real.log 5756 - Real.log (Real.log 5756)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (133000 : ℝ) / 1000 ≤
        Real.sqrt 5867 *
          (Real.log 5867 * (Real.log 5867 - Real.log (Real.log 5867)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (133000 : ℝ) / 1000 ≤
        Real.sqrt 6011 *
          (Real.log 6011 * (Real.log 6011 - Real.log (Real.log 6011)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)

/-- The envelope bound applies at every cell b endpoint. -/
private theorem batch_b :
    ∀ r ∈ batchCells,
      (r.cb : ℝ) / 1000 ≤
        Real.sqrt r.b *
          (Real.log r.b * (Real.log r.b - Real.log (Real.log r.b)) / (8 * Real.pi)) := by
  intro r hr
  simp only [batchCells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl
  · change
      (133000 : ℝ) / 1000 ≤
        Real.sqrt 4397 *
          (Real.log 4397 * (Real.log 4397 - Real.log (Real.log 4397)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (133000 : ℝ) / 1000 ≤
        Real.sqrt 4523 *
          (Real.log 4523 * (Real.log 4523 - Real.log (Real.log 4523)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (133000 : ℝ) / 1000 ≤
        Real.sqrt 4657 *
          (Real.log 4657 * (Real.log 4657 - Real.log (Real.log 4657)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (133000 : ℝ) / 1000 ≤
        Real.sqrt 4793 *
          (Real.log 4793 * (Real.log 4793 - Real.log (Real.log 4793)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (133000 : ℝ) / 1000 ≤
        Real.sqrt 4924 *
          (Real.log 4924 * (Real.log 4924 - Real.log (Real.log 4924)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (133000 : ℝ) / 1000 ≤
        Real.sqrt 5028 *
          (Real.log 5028 * (Real.log 5028 - Real.log (Real.log 5028)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (133000 : ℝ) / 1000 ≤
        Real.sqrt 5167 *
          (Real.log 5167 * (Real.log 5167 - Real.log (Real.log 5167)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (133000 : ℝ) / 1000 ≤
        Real.sqrt 5296 *
          (Real.log 5296 * (Real.log 5296 - Real.log (Real.log 5296)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (133000 : ℝ) / 1000 ≤
        Real.sqrt 5408 *
          (Real.log 5408 * (Real.log 5408 - Real.log (Real.log 5408)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (133000 : ℝ) / 1000 ≤
        Real.sqrt 5515 *
          (Real.log 5515 * (Real.log 5515 - Real.log (Real.log 5515)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (133000 : ℝ) / 1000 ≤
        Real.sqrt 5644 *
          (Real.log 5644 * (Real.log 5644 - Real.log (Real.log 5644)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (133000 : ℝ) / 1000 ≤
        Real.sqrt 5756 *
          (Real.log 5756 * (Real.log 5756 - Real.log (Real.log 5756)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (133000 : ℝ) / 1000 ≤
        Real.sqrt 5867 *
          (Real.log 5867 * (Real.log 5867 - Real.log (Real.log 5867)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (133000 : ℝ) / 1000 ≤
        Real.sqrt 6011 *
          (Real.log 6011 * (Real.log 6011 - Real.log (Real.log 6011)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (133000 : ℝ) / 1000 ≤
        Real.sqrt 6138 *
          (Real.log 6138 * (Real.log 6138 - Real.log (Real.log 6138)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)

/-- The checked batch proves the Lee–Nosal psi estimate on `[4259, 6138)`. -/
theorem psi_lee_nosal_4259_6138 {x : ℝ} (ha : 4259 ≤ x) (hb : x < 6138) :
    |Chebyshev.psi x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  exact
    lee_nosal_chain_sound Chebyshev.psi_mono Chebyshev.psi_eq_psi_coe_floor (by decide +kernel)
      batch_lower batch_upper batch_a batch_b ha hb

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
