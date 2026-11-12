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
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSmallDefect7776
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalEnvelope5625
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalMonotone
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalChecker

/-! # Batch certificate for Lee–Nosal theta cells -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The local cells store endpoint bounds in thousandths. -/
def theta5625Cells : List LeeNosalCell :=
  [⟨5625, 5658, 5493187, 5658854, 165000, 165000⟩, ⟨5658, 5709, 5544480, 5710840, 165000, 165000⟩,
    ⟨5709, 5761, 5596466, 5762826, 165000, 165000⟩, ⟨5761, 5813, 5648452, 5806494, 165000, 165000⟩,
    ⟨5813, 5865, 5700438, 5884127, 165000, 165000⟩, ⟨5865, 5934, 5769753, 5953442, 165000, 165000⟩,
    ⟨5934, 6004, 5839067, 5988792, 165000, 165000⟩, ⟨6004, 6039, 5874418, 6023450, 165000, 165000⟩,
    ⟨6039, 6074, 5909075, 6067118, 165000, 165000⟩, ⟨6074, 6117, 5952744, 6110093, 165000, 165000⟩,
    ⟨6117, 6160, 5995719, 6153761, 165000, 165000⟩, ⟨6160, 6204, 6039387, 6197429, 165000, 165000⟩]

/-- The kernel-checked prefix bounds for 5623. -/
theorem theta5625_psi_5623_bounds :
    (5606867 : ℝ) / 1000 ≤ Chebyshev.psi 5623 ∧ Chebyshev.psi 5623 ≤ (5607561 : ℝ) / 1000 := by
  have hl : 2 ^ 8089 ≤ Nat.lcmUpto 5623 := by decide +kernel
  have hu : Nat.lcmUpto 5623 ≤ 2 ^ (8089 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 5657. -/
theorem theta5625_psi_5657_bounds :
    (5658160 : ℝ) / 1000 ≤ Chebyshev.psi 5657 ∧ Chebyshev.psi 5657 ≤ (5658854 : ℝ) / 1000 := by
  have hl : 2 ^ 8163 ≤ Nat.lcmUpto 5657 := by decide +kernel
  have hu : Nat.lcmUpto 5657 ≤ 2 ^ (8163 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 5701. -/
theorem theta5625_psi_5701_bounds :
    (5710146 : ℝ) / 1000 ≤ Chebyshev.psi 5701 ∧ Chebyshev.psi 5701 ≤ (5710840 : ℝ) / 1000 := by
  have hl : 2 ^ 8238 ≤ Nat.lcmUpto 5701 := by decide +kernel
  have hu : Nat.lcmUpto 5701 ≤ 2 ^ (8238 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 5749. -/
theorem theta5625_psi_5749_bounds :
    (5762132 : ℝ) / 1000 ≤ Chebyshev.psi 5749 ∧ Chebyshev.psi 5749 ≤ (5762826 : ℝ) / 1000 := by
  have hl : 2 ^ 8313 ≤ Nat.lcmUpto 5749 := by decide +kernel
  have hu : Nat.lcmUpto 5749 ≤ 2 ^ (8313 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 5807. -/
theorem theta5625_psi_5807_bounds :
    (5805800 : ℝ) / 1000 ≤ Chebyshev.psi 5807 ∧ Chebyshev.psi 5807 ≤ (5806494 : ℝ) / 1000 := by
  have hl : 2 ^ 8376 ≤ Nat.lcmUpto 5807 := by decide +kernel
  have hu : Nat.lcmUpto 5807 ≤ 2 ^ (8376 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 5813. -/
theorem theta5625_psi_5813_bounds :
    (5814118 : ℝ) / 1000 ≤ Chebyshev.psi 5813 ∧ Chebyshev.psi 5813 ≤ (5814812 : ℝ) / 1000 := by
  have hl : 2 ^ 8388 ≤ Nat.lcmUpto 5813 := by decide +kernel
  have hu : Nat.lcmUpto 5813 ≤ 2 ^ (8388 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 5861. -/
theorem theta5625_psi_5861_bounds :
    (5883433 : ℝ) / 1000 ≤ Chebyshev.psi 5861 ∧ Chebyshev.psi 5861 ≤ (5884127 : ℝ) / 1000 := by
  have hl : 2 ^ 8488 ≤ Nat.lcmUpto 5861 := by decide +kernel
  have hu : Nat.lcmUpto 5861 ≤ 2 ^ (8488 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 5927. -/
theorem theta5625_psi_5927_bounds :
    (5952747 : ℝ) / 1000 ≤ Chebyshev.psi 5927 ∧ Chebyshev.psi 5927 ≤ (5953442 : ℝ) / 1000 := by
  have hl : 2 ^ 8588 ≤ Nat.lcmUpto 5927 := by decide +kernel
  have hu : Nat.lcmUpto 5927 ≤ 2 ^ (8588 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 5987. -/
theorem theta5625_psi_5987_bounds :
    (5988098 : ℝ) / 1000 ≤ Chebyshev.psi 5987 ∧ Chebyshev.psi 5987 ≤ (5988792 : ℝ) / 1000 := by
  have hl : 2 ^ 8639 ≤ Nat.lcmUpto 5987 := by decide +kernel
  have hu : Nat.lcmUpto 5987 ≤ 2 ^ (8639 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 6037. -/
theorem theta5625_psi_6037_bounds :
    (6022755 : ℝ) / 1000 ≤ Chebyshev.psi 6037 ∧ Chebyshev.psi 6037 ≤ (6023450 : ℝ) / 1000 := by
  have hl : 2 ^ 8689 ≤ Nat.lcmUpto 6037 := by decide +kernel
  have hu : Nat.lcmUpto 6037 ≤ 2 ^ (8689 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 6073. -/
theorem theta5625_psi_6073_bounds :
    (6066424 : ℝ) / 1000 ≤ Chebyshev.psi 6073 ∧ Chebyshev.psi 6073 ≤ (6067118 : ℝ) / 1000 := by
  have hl : 2 ^ 8752 ≤ Nat.lcmUpto 6073 := by decide +kernel
  have hu : Nat.lcmUpto 6073 ≤ 2 ^ (8752 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 6113. -/
theorem theta5625_psi_6113_bounds :
    (6109399 : ℝ) / 1000 ≤ Chebyshev.psi 6113 ∧ Chebyshev.psi 6113 ≤ (6110093 : ℝ) / 1000 := by
  have hl : 2 ^ 8814 ≤ Nat.lcmUpto 6113 := by decide +kernel
  have hu : Nat.lcmUpto 6113 ≤ 2 ^ (8814 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 6151. -/
theorem theta5625_psi_6151_bounds :
    (6153067 : ℝ) / 1000 ≤ Chebyshev.psi 6151 ∧ Chebyshev.psi 6151 ≤ (6153761 : ℝ) / 1000 := by
  have hl : 2 ^ 8877 ≤ Nat.lcmUpto 6151 := by decide +kernel
  have hu : Nat.lcmUpto 6151 ≤ 2 ^ (8877 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 6203. -/
theorem theta5625_psi_6203_bounds :
    (6196735 : ℝ) / 1000 ≤ Chebyshev.psi 6203 ∧ Chebyshev.psi 6203 ≤ (6197429 : ℝ) / 1000 := by
  have hl : 2 ^ 8940 ≤ Nat.lcmUpto 6203 := by decide +kernel
  have hu : Nat.lcmUpto 6203 ≤ 2 ^ (8940 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- Every batch cell has a checked theta lower bound. -/
theorem theta5625_lower : ∀ r ∈ theta5625Cells, (r.lo : ℝ) / 1000 ≤ Chebyshev.theta r.a := by
  intro r hr
  simp only [theta5625Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change (5493187 : ℝ) / 1000 ≤ Chebyshev.theta (↑(5625 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_11368 (x := 5625) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 5623) (b := 5625) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta5625_psi_5623_bounds.1]
  · change (5544480 : ℝ) / 1000 ≤ Chebyshev.theta (↑(5658 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_11368 (x := 5658) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 5657) (b := 5658) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta5625_psi_5657_bounds.1]
  · change (5596466 : ℝ) / 1000 ≤ Chebyshev.theta (↑(5709 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_11368 (x := 5709) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 5701) (b := 5709) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta5625_psi_5701_bounds.1]
  · change (5648452 : ℝ) / 1000 ≤ Chebyshev.theta (↑(5761 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_11368 (x := 5761) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 5749) (b := 5761) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta5625_psi_5749_bounds.1]
  · change (5700438 : ℝ) / 1000 ≤ Chebyshev.theta (↑(5813 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_11368 (x := 5813) (by norm_num only) (by norm_num only)
    linarith only [hd, theta5625_psi_5813_bounds.1]
  · change (5769753 : ℝ) / 1000 ≤ Chebyshev.theta (↑(5865 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_11368 (x := 5865) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 5861) (b := 5865) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta5625_psi_5861_bounds.1]
  · change (5839067 : ℝ) / 1000 ≤ Chebyshev.theta (↑(5934 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_11368 (x := 5934) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 5927) (b := 5934) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta5625_psi_5927_bounds.1]
  · change (5874418 : ℝ) / 1000 ≤ Chebyshev.theta (↑(6004 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_11368 (x := 6004) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 5987) (b := 6004) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta5625_psi_5987_bounds.1]
  · change (5909075 : ℝ) / 1000 ≤ Chebyshev.theta (↑(6039 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_11368 (x := 6039) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 6037) (b := 6039) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta5625_psi_6037_bounds.1]
  · change (5952744 : ℝ) / 1000 ≤ Chebyshev.theta (↑(6074 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_11368 (x := 6074) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 6073) (b := 6074) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta5625_psi_6073_bounds.1]
  · change (5995719 : ℝ) / 1000 ≤ Chebyshev.theta (↑(6117 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_11368 (x := 6117) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 6113) (b := 6117) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta5625_psi_6113_bounds.1]
  · change (6039387 : ℝ) / 1000 ≤ Chebyshev.theta (↑(6160 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_11368 (x := 6160) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 6151) (b := 6160) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta5625_psi_6151_bounds.1]

/-- Every batch cell has a checked theta upper bound. -/
theorem theta5625_upper :
    ∀ r ∈ theta5625Cells, Chebyshev.theta (r.b - 1 : ℕ) ≤ (r.hi : ℝ) / 1000 := by
  intro r hr
  simp only [theta5625Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change Chebyshev.theta (↑(5657 : ℕ) : ℝ) ≤ (5658854 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 5657
    linarith only [hd, theta5625_psi_5657_bounds.2]
  · change Chebyshev.theta (↑(5708 : ℕ) : ℝ) ≤ (5710840 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 5708
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 5701) (b := 5708) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta5625_psi_5701_bounds.2]
  · change Chebyshev.theta (↑(5760 : ℕ) : ℝ) ≤ (5762826 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 5760
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 5749) (b := 5760) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta5625_psi_5749_bounds.2]
  · change Chebyshev.theta (↑(5812 : ℕ) : ℝ) ≤ (5806494 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 5812
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 5807) (b := 5812) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta5625_psi_5807_bounds.2]
  · change Chebyshev.theta (↑(5864 : ℕ) : ℝ) ≤ (5884127 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 5864
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 5861) (b := 5864) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta5625_psi_5861_bounds.2]
  · change Chebyshev.theta (↑(5933 : ℕ) : ℝ) ≤ (5953442 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 5933
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 5927) (b := 5933) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta5625_psi_5927_bounds.2]
  · change Chebyshev.theta (↑(6003 : ℕ) : ℝ) ≤ (5988792 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 6003
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 5987) (b := 6003) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta5625_psi_5987_bounds.2]
  · change Chebyshev.theta (↑(6038 : ℕ) : ℝ) ≤ (6023450 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 6038
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 6037) (b := 6038) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta5625_psi_6037_bounds.2]
  · change Chebyshev.theta (↑(6073 : ℕ) : ℝ) ≤ (6067118 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 6073
    linarith only [hd, theta5625_psi_6073_bounds.2]
  · change Chebyshev.theta (↑(6116 : ℕ) : ℝ) ≤ (6110093 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 6116
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 6113) (b := 6116) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta5625_psi_6113_bounds.2]
  · change Chebyshev.theta (↑(6159 : ℕ) : ℝ) ≤ (6153761 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 6159
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 6151) (b := 6159) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta5625_psi_6151_bounds.2]
  · change Chebyshev.theta (↑(6203 : ℕ) : ℝ) ≤ (6197429 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 6203
    linarith only [hd, theta5625_psi_6203_bounds.2]

/-- The envelope bound applies at every cell a endpoint. -/
theorem theta5625_a :
    ∀ r ∈ theta5625Cells,
      (r.ca : ℝ) / 1000 ≤
        Real.sqrt r.a *
          (Real.log r.a * (Real.log r.a - Real.log (Real.log r.a)) / (8 * Real.pi)) := by
  intro r hr
  simp only [theta5625Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 5625 *
          (Real.log 5625 * (Real.log 5625 - Real.log (Real.log 5625)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 5658 *
          (Real.log 5658 * (Real.log 5658 - Real.log (Real.log 5658)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 5709 *
          (Real.log 5709 * (Real.log 5709 - Real.log (Real.log 5709)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 5761 *
          (Real.log 5761 * (Real.log 5761 - Real.log (Real.log 5761)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 5813 *
          (Real.log 5813 * (Real.log 5813 - Real.log (Real.log 5813)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 5865 *
          (Real.log 5865 * (Real.log 5865 - Real.log (Real.log 5865)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 5934 *
          (Real.log 5934 * (Real.log 5934 - Real.log (Real.log 5934)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 6004 *
          (Real.log 6004 * (Real.log 6004 - Real.log (Real.log 6004)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 6039 *
          (Real.log 6039 * (Real.log 6039 - Real.log (Real.log 6039)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 6074 *
          (Real.log 6074 * (Real.log 6074 - Real.log (Real.log 6074)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 6117 *
          (Real.log 6117 * (Real.log 6117 - Real.log (Real.log 6117)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 6160 *
          (Real.log 6160 * (Real.log 6160 - Real.log (Real.log 6160)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)

/-- The envelope bound applies at every cell b endpoint. -/
theorem theta5625_b :
    ∀ r ∈ theta5625Cells,
      (r.cb : ℝ) / 1000 ≤
        Real.sqrt r.b *
          (Real.log r.b * (Real.log r.b - Real.log (Real.log r.b)) / (8 * Real.pi)) := by
  intro r hr
  simp only [theta5625Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 5658 *
          (Real.log 5658 * (Real.log 5658 - Real.log (Real.log 5658)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 5709 *
          (Real.log 5709 * (Real.log 5709 - Real.log (Real.log 5709)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 5761 *
          (Real.log 5761 * (Real.log 5761 - Real.log (Real.log 5761)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 5813 *
          (Real.log 5813 * (Real.log 5813 - Real.log (Real.log 5813)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 5865 *
          (Real.log 5865 * (Real.log 5865 - Real.log (Real.log 5865)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 5934 *
          (Real.log 5934 * (Real.log 5934 - Real.log (Real.log 5934)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 6004 *
          (Real.log 6004 * (Real.log 6004 - Real.log (Real.log 6004)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 6039 *
          (Real.log 6039 * (Real.log 6039 - Real.log (Real.log 6039)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 6074 *
          (Real.log 6074 * (Real.log 6074 - Real.log (Real.log 6074)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 6117 *
          (Real.log 6117 * (Real.log 6117 - Real.log (Real.log 6117)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 6160 *
          (Real.log 6160 * (Real.log 6160 - Real.log (Real.log 6160)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 6204 *
          (Real.log 6204 * (Real.log 6204 - Real.log (Real.log 6204)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)

/-- The cells form a checked chain covering `[5625, 6204)`. -/
theorem theta5625_check : leeNosalChainCheck 5625 6204 theta5625Cells = true := by decide +kernel

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
