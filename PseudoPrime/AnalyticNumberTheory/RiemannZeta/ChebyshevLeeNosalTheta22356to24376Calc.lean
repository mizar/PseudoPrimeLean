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
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSmallDefect32768
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalEnvelope16384
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalMonotone
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalChecker

/-! # Batch certificate for Lee–Nosal theta cells -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The local cells store endpoint bounds in thousandths. -/
def theta22356Cells : List LeeNosalCell :=
  [⟨22356, 22511, 22146718, 22512728, 365000, 365000⟩,
    ⟨22511, 22661, 22296438, 22663141, 365000, 365000⟩,
    ⟨22661, 22802, 22437147, 22828803, 365000, 365000⟩,
    ⟨22802, 22967, 22602809, 22979216, 365000, 365000⟩,
    ⟨22967, 23118, 22753222, 23169831, 365000, 365000⟩,
    ⟨23118, 23308, 22943837, 23341039, 365000, 365000⟩,
    ⟨23308, 23480, 23115045, 23481748, 365000, 365000⟩,
    ⟨23480, 23620, 23255753, 23632854, 365000, 365000⟩,
    ⟨23620, 23771, 23406859, 23804061, 365000, 365000⟩,
    ⟨23771, 23943, 23578067, 23995370, 365000, 365000⟩,
    ⟨23943, 24134, 23769375, 24237278, 365000, 365000⟩,
    ⟨24134, 24376, 24011284, 24429280, 365000, 365000⟩]

/-- The kernel-checked prefix bounds for 22349. -/
theorem theta22356_psi_22349_bounds :
    (22372018 : ℝ) / 1000 ≤ Chebyshev.psi 22349 ∧ Chebyshev.psi 22349 ≤ (22372712 : ℝ) / 1000 := by
  have hl : 2 ^ 32276 ≤ Nat.lcmUpto 22349 := by decide +kernel
  have hu : Nat.lcmUpto 22349 ≤ 2 ^ (32276 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 22501. -/
theorem theta22356_psi_22501_bounds :
    (22512034 : ℝ) / 1000 ≤ Chebyshev.psi 22501 ∧ Chebyshev.psi 22501 ≤ (22512728 : ℝ) / 1000 := by
  have hl : 2 ^ 32478 ≤ Nat.lcmUpto 22501 := by decide +kernel
  have hu : Nat.lcmUpto 22501 ≤ 2 ^ (32478 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 22511. -/
theorem theta22356_psi_22511_bounds :
    (22521738 : ℝ) / 1000 ≤ Chebyshev.psi 22511 ∧ Chebyshev.psi 22511 ≤ (22522432 : ℝ) / 1000 := by
  have hl : 2 ^ 32492 ≤ Nat.lcmUpto 22511 := by decide +kernel
  have hu : Nat.lcmUpto 22511 ≤ 2 ^ (32492 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 22651. -/
theorem theta22356_psi_22651_bounds :
    (22662447 : ℝ) / 1000 ≤ Chebyshev.psi 22651 ∧ Chebyshev.psi 22651 ≤ (22663141 : ℝ) / 1000 := by
  have hl : 2 ^ 32695 ≤ Nat.lcmUpto 22651 := by decide +kernel
  have hu : Nat.lcmUpto 22651 ≤ 2 ^ (32695 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 22801. -/
theorem theta22356_psi_22801_bounds :
    (22828109 : ℝ) / 1000 ≤ Chebyshev.psi 22801 ∧ Chebyshev.psi 22801 ≤ (22828803 : ℝ) / 1000 := by
  have hl : 2 ^ 32934 ≤ Nat.lcmUpto 22801 := by decide +kernel
  have hu : Nat.lcmUpto 22801 ≤ 2 ^ (32934 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 22963. -/
theorem theta22356_psi_22963_bounds :
    (22978522 : ℝ) / 1000 ≤ Chebyshev.psi 22963 ∧ Chebyshev.psi 22963 ≤ (22979216 : ℝ) / 1000 := by
  have hl : 2 ^ 33151 ≤ Nat.lcmUpto 22963 := by decide +kernel
  have hu : Nat.lcmUpto 22963 ≤ 2 ^ (33151 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 23117. -/
theorem theta22356_psi_23117_bounds :
    (23169137 : ℝ) / 1000 ≤ Chebyshev.psi 23117 ∧ Chebyshev.psi 23117 ≤ (23169831 : ℝ) / 1000 := by
  have hl : 2 ^ 33426 ≤ Nat.lcmUpto 23117 := by decide +kernel
  have hu : Nat.lcmUpto 23117 ≤ 2 ^ (33426 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 23297. -/
theorem theta22356_psi_23297_bounds :
    (23340345 : ℝ) / 1000 ≤ Chebyshev.psi 23297 ∧ Chebyshev.psi 23297 ≤ (23341039 : ℝ) / 1000 := by
  have hl : 2 ^ 33673 ≤ Nat.lcmUpto 23297 := by decide +kernel
  have hu : Nat.lcmUpto 23297 ≤ 2 ^ (33673 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 23473. -/
theorem theta22356_psi_23473_bounds :
    (23481053 : ℝ) / 1000 ≤ Chebyshev.psi 23473 ∧ Chebyshev.psi 23473 ≤ (23481748 : ℝ) / 1000 := by
  have hl : 2 ^ 33876 ≤ Nat.lcmUpto 23473 := by decide +kernel
  have hu : Nat.lcmUpto 23473 ≤ 2 ^ (33876 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 23609. -/
theorem theta22356_psi_23609_bounds :
    (23632159 : ℝ) / 1000 ≤ Chebyshev.psi 23609 ∧ Chebyshev.psi 23609 ≤ (23632854 : ℝ) / 1000 := by
  have hl : 2 ^ 34094 ≤ Nat.lcmUpto 23609 := by decide +kernel
  have hu : Nat.lcmUpto 23609 ≤ 2 ^ (34094 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 23767. -/
theorem theta22356_psi_23767_bounds :
    (23803367 : ℝ) / 1000 ≤ Chebyshev.psi 23767 ∧ Chebyshev.psi 23767 ≤ (23804061 : ℝ) / 1000 := by
  have hl : 2 ^ 34341 ≤ Nat.lcmUpto 23767 := by decide +kernel
  have hu : Nat.lcmUpto 23767 ≤ 2 ^ (34341 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 23929. -/
theorem theta22356_psi_23929_bounds :
    (23994675 : ℝ) / 1000 ≤ Chebyshev.psi 23929 ∧ Chebyshev.psi 23929 ≤ (23995370 : ℝ) / 1000 := by
  have hl : 2 ^ 34617 ≤ Nat.lcmUpto 23929 := by decide +kernel
  have hu : Nat.lcmUpto 23929 ≤ 2 ^ (34617 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 24133. -/
theorem theta22356_psi_24133_bounds :
    (24236584 : ℝ) / 1000 ≤ Chebyshev.psi 24133 ∧ Chebyshev.psi 24133 ≤ (24237278 : ℝ) / 1000 := by
  have hl : 2 ^ 34966 ≤ Nat.lcmUpto 24133 := by decide +kernel
  have hu : Nat.lcmUpto 24133 ≤ 2 ^ (34966 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 24373. -/
theorem theta22356_psi_24373_bounds :
    (24428586 : ℝ) / 1000 ≤ Chebyshev.psi 24373 ∧ Chebyshev.psi 24373 ≤ (24429280 : ℝ) / 1000 := by
  have hl : 2 ^ 35243 ≤ Nat.lcmUpto 24373 := by decide +kernel
  have hu : Nat.lcmUpto 24373 ≤ 2 ^ (35243 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- Every batch cell has a checked theta lower bound. -/
theorem theta22356_lower : ∀ r ∈ theta22356Cells, (r.lo : ℝ) / 1000 ≤ Chebyshev.theta r.a := by
  intro r hr
  simp only [theta22356Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change (22146718 : ℝ) / 1000 ≤ Chebyshev.theta (↑(22356 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 22356) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 22349) (b := 22356) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta22356_psi_22349_bounds.1]
  · change (22296438 : ℝ) / 1000 ≤ Chebyshev.theta (↑(22511 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 22511) (by norm_num only) (by norm_num only)
    linarith only [hd, theta22356_psi_22511_bounds.1]
  · change (22437147 : ℝ) / 1000 ≤ Chebyshev.theta (↑(22661 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 22661) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 22651) (b := 22661) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta22356_psi_22651_bounds.1]
  · change (22602809 : ℝ) / 1000 ≤ Chebyshev.theta (↑(22802 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 22802) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 22801) (b := 22802) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta22356_psi_22801_bounds.1]
  · change (22753222 : ℝ) / 1000 ≤ Chebyshev.theta (↑(22967 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 22967) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 22963) (b := 22967) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta22356_psi_22963_bounds.1]
  · change (22943837 : ℝ) / 1000 ≤ Chebyshev.theta (↑(23118 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 23118) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 23117) (b := 23118) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta22356_psi_23117_bounds.1]
  · change (23115045 : ℝ) / 1000 ≤ Chebyshev.theta (↑(23308 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 23308) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 23297) (b := 23308) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta22356_psi_23297_bounds.1]
  · change (23255753 : ℝ) / 1000 ≤ Chebyshev.theta (↑(23480 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 23480) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 23473) (b := 23480) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta22356_psi_23473_bounds.1]
  · change (23406859 : ℝ) / 1000 ≤ Chebyshev.theta (↑(23620 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 23620) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 23609) (b := 23620) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta22356_psi_23609_bounds.1]
  · change (23578067 : ℝ) / 1000 ≤ Chebyshev.theta (↑(23771 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 23771) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 23767) (b := 23771) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta22356_psi_23767_bounds.1]
  · change (23769375 : ℝ) / 1000 ≤ Chebyshev.theta (↑(23943 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 23943) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 23929) (b := 23943) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta22356_psi_23929_bounds.1]
  · change (24011284 : ℝ) / 1000 ≤ Chebyshev.theta (↑(24134 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 24134) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 24133) (b := 24134) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta22356_psi_24133_bounds.1]

/-- Every batch cell has a checked theta upper bound. -/
theorem theta22356_upper :
    ∀ r ∈ theta22356Cells, Chebyshev.theta (r.b - 1 : ℕ) ≤ (r.hi : ℝ) / 1000 := by
  intro r hr
  simp only [theta22356Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change Chebyshev.theta (↑(22510 : ℕ) : ℝ) ≤ (22512728 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 22510
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 22501) (b := 22510) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta22356_psi_22501_bounds.2]
  · change Chebyshev.theta (↑(22660 : ℕ) : ℝ) ≤ (22663141 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 22660
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 22651) (b := 22660) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta22356_psi_22651_bounds.2]
  · change Chebyshev.theta (↑(22801 : ℕ) : ℝ) ≤ (22828803 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 22801
    linarith only [hd, theta22356_psi_22801_bounds.2]
  · change Chebyshev.theta (↑(22966 : ℕ) : ℝ) ≤ (22979216 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 22966
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 22963) (b := 22966) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta22356_psi_22963_bounds.2]
  · change Chebyshev.theta (↑(23117 : ℕ) : ℝ) ≤ (23169831 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 23117
    linarith only [hd, theta22356_psi_23117_bounds.2]
  · change Chebyshev.theta (↑(23307 : ℕ) : ℝ) ≤ (23341039 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 23307
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 23297) (b := 23307) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta22356_psi_23297_bounds.2]
  · change Chebyshev.theta (↑(23479 : ℕ) : ℝ) ≤ (23481748 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 23479
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 23473) (b := 23479) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta22356_psi_23473_bounds.2]
  · change Chebyshev.theta (↑(23619 : ℕ) : ℝ) ≤ (23632854 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 23619
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 23609) (b := 23619) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta22356_psi_23609_bounds.2]
  · change Chebyshev.theta (↑(23770 : ℕ) : ℝ) ≤ (23804061 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 23770
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 23767) (b := 23770) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta22356_psi_23767_bounds.2]
  · change Chebyshev.theta (↑(23942 : ℕ) : ℝ) ≤ (23995370 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 23942
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 23929) (b := 23942) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta22356_psi_23929_bounds.2]
  · change Chebyshev.theta (↑(24133 : ℕ) : ℝ) ≤ (24237278 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 24133
    linarith only [hd, theta22356_psi_24133_bounds.2]
  · change Chebyshev.theta (↑(24375 : ℕ) : ℝ) ≤ (24429280 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 24375
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 24373) (b := 24375) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta22356_psi_24373_bounds.2]

/-- The envelope bound applies at every cell a endpoint. -/
theorem theta22356_a :
    ∀ r ∈ theta22356Cells,
      (r.ca : ℝ) / 1000 ≤
        Real.sqrt r.a *
          (Real.log r.a * (Real.log r.a - Real.log (Real.log r.a)) / (8 * Real.pi)) := by
  intro r hr
  simp only [theta22356Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 22356 *
          (Real.log 22356 * (Real.log 22356 - Real.log (Real.log 22356)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 22511 *
          (Real.log 22511 * (Real.log 22511 - Real.log (Real.log 22511)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 22661 *
          (Real.log 22661 * (Real.log 22661 - Real.log (Real.log 22661)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 22802 *
          (Real.log 22802 * (Real.log 22802 - Real.log (Real.log 22802)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 22967 *
          (Real.log 22967 * (Real.log 22967 - Real.log (Real.log 22967)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 23118 *
          (Real.log 23118 * (Real.log 23118 - Real.log (Real.log 23118)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 23308 *
          (Real.log 23308 * (Real.log 23308 - Real.log (Real.log 23308)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 23480 *
          (Real.log 23480 * (Real.log 23480 - Real.log (Real.log 23480)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 23620 *
          (Real.log 23620 * (Real.log 23620 - Real.log (Real.log 23620)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 23771 *
          (Real.log 23771 * (Real.log 23771 - Real.log (Real.log 23771)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 23943 *
          (Real.log 23943 * (Real.log 23943 - Real.log (Real.log 23943)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 24134 *
          (Real.log 24134 * (Real.log 24134 - Real.log (Real.log 24134)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)

/-- The envelope bound applies at every cell b endpoint. -/
theorem theta22356_b :
    ∀ r ∈ theta22356Cells,
      (r.cb : ℝ) / 1000 ≤
        Real.sqrt r.b *
          (Real.log r.b * (Real.log r.b - Real.log (Real.log r.b)) / (8 * Real.pi)) := by
  intro r hr
  simp only [theta22356Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 22511 *
          (Real.log 22511 * (Real.log 22511 - Real.log (Real.log 22511)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 22661 *
          (Real.log 22661 * (Real.log 22661 - Real.log (Real.log 22661)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 22802 *
          (Real.log 22802 * (Real.log 22802 - Real.log (Real.log 22802)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 22967 *
          (Real.log 22967 * (Real.log 22967 - Real.log (Real.log 22967)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 23118 *
          (Real.log 23118 * (Real.log 23118 - Real.log (Real.log 23118)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 23308 *
          (Real.log 23308 * (Real.log 23308 - Real.log (Real.log 23308)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 23480 *
          (Real.log 23480 * (Real.log 23480 - Real.log (Real.log 23480)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 23620 *
          (Real.log 23620 * (Real.log 23620 - Real.log (Real.log 23620)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 23771 *
          (Real.log 23771 * (Real.log 23771 - Real.log (Real.log 23771)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 23943 *
          (Real.log 23943 * (Real.log 23943 - Real.log (Real.log 23943)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 24134 *
          (Real.log 24134 * (Real.log 24134 - Real.log (Real.log 24134)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 24376 *
          (Real.log 24376 * (Real.log 24376 - Real.log (Real.log 24376)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)

/-- The cells form a checked chain covering `[22356, 24376)`. -/
theorem theta22356_check : leeNosalChainCheck 22356 24376 theta22356Cells = true := by
  decide +kernel

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
