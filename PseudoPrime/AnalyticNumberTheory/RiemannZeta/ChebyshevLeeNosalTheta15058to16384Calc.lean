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
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSmallDefect16384
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalEnvelope10000
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalMonotone
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalChecker

/-! # Batch certificate for Lee–Nosal theta cells -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The local cells store endpoint bounds in thousandths. -/
def theta15058Cells : List LeeNosalCell :=
  [⟨15058, 15126, 14871450, 15107143, 255000, 255000⟩,
    ⟨15126, 15203, 14948389, 15193787, 255000, 255000⟩,
    ⟨15203, 15290, 15035033, 15299145, 255000, 255000⟩,
    ⟨15290, 15395, 15140391, 15424605, 255000, 255000⟩,
    ⟨15395, 15520, 15265851, 15540360, 255000, 255000⟩,
    ⟨15520, 15636, 15381606, 15648491, 255000, 255000⟩,
    ⟨15636, 15744, 15489737, 15783655, 255000, 255000⟩,
    ⟨15744, 15879, 15624901, 15909115, 255000, 255000⟩,
    ⟨15879, 16005, 15750360, 16044971, 255000, 255000⟩,
    ⟨16005, 16141, 15886217, 16194691, 255000, 255000⟩,
    ⟨16141, 16300, 16045641, 16320844, 255000, 255000⟩,
    ⟨16300, 16384, 16162090, 16408181, 255000, 255000⟩]

/-- The kernel-checked prefix bounds for 15053. -/
theorem theta15058_psi_15053_bounds :
    (15029510 : ℝ) / 1000 ≤ Chebyshev.psi 15053 ∧ Chebyshev.psi 15053 ≤ (15030204 : ℝ) / 1000 := by
  have hl : 2 ^ 21683 ≤ Nat.lcmUpto 15053 := by decide +kernel
  have hu : Nat.lcmUpto 15053 ≤ 2 ^ (21683 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 15121. -/
theorem theta15058_psi_15121_bounds :
    (15106449 : ℝ) / 1000 ≤ Chebyshev.psi 15121 ∧ Chebyshev.psi 15121 ≤ (15107143 : ℝ) / 1000 := by
  have hl : 2 ^ 21794 ≤ Nat.lcmUpto 15121 := by decide +kernel
  have hu : Nat.lcmUpto 15121 ≤ 2 ^ (21794 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 15199. -/
theorem theta15058_psi_15199_bounds :
    (15193093 : ℝ) / 1000 ≤ Chebyshev.psi 15199 ∧ Chebyshev.psi 15199 ≤ (15193787 : ℝ) / 1000 := by
  have hl : 2 ^ 21919 ≤ Nat.lcmUpto 15199 := by decide +kernel
  have hu : Nat.lcmUpto 15199 ≤ 2 ^ (21919 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 15289. -/
theorem theta15058_psi_15289_bounds :
    (15298451 : ℝ) / 1000 ≤ Chebyshev.psi 15289 ∧ Chebyshev.psi 15289 ≤ (15299145 : ℝ) / 1000 := by
  have hl : 2 ^ 22071 ≤ Nat.lcmUpto 15289 := by decide +kernel
  have hu : Nat.lcmUpto 15289 ≤ 2 ^ (22071 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 15391. -/
theorem theta15058_psi_15391_bounds :
    (15423911 : ℝ) / 1000 ≤ Chebyshev.psi 15391 ∧ Chebyshev.psi 15391 ≤ (15424605 : ℝ) / 1000 := by
  have hl : 2 ^ 22252 ≤ Nat.lcmUpto 15391 := by decide +kernel
  have hu : Nat.lcmUpto 15391 ≤ 2 ^ (22252 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 15511. -/
theorem theta15058_psi_15511_bounds :
    (15539666 : ℝ) / 1000 ≤ Chebyshev.psi 15511 ∧ Chebyshev.psi 15511 ≤ (15540360 : ℝ) / 1000 := by
  have hl : 2 ^ 22419 ≤ Nat.lcmUpto 15511 := by decide +kernel
  have hu : Nat.lcmUpto 15511 ≤ 2 ^ (22419 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 15629. -/
theorem theta15058_psi_15629_bounds :
    (15647797 : ℝ) / 1000 ≤ Chebyshev.psi 15629 ∧ Chebyshev.psi 15629 ≤ (15648491 : ℝ) / 1000 := by
  have hl : 2 ^ 22575 ≤ Nat.lcmUpto 15629 := by decide +kernel
  have hu : Nat.lcmUpto 15629 ≤ 2 ^ (22575 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 15739. -/
theorem theta15058_psi_15739_bounds :
    (15782961 : ℝ) / 1000 ≤ Chebyshev.psi 15739 ∧ Chebyshev.psi 15739 ≤ (15783655 : ℝ) / 1000 := by
  have hl : 2 ^ 22770 ≤ Nat.lcmUpto 15739 := by decide +kernel
  have hu : Nat.lcmUpto 15739 ≤ 2 ^ (22770 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 15877. -/
theorem theta15058_psi_15877_bounds :
    (15908420 : ℝ) / 1000 ≤ Chebyshev.psi 15877 ∧ Chebyshev.psi 15877 ≤ (15909115 : ℝ) / 1000 := by
  have hl : 2 ^ 22951 ≤ Nat.lcmUpto 15877 := by decide +kernel
  have hu : Nat.lcmUpto 15877 ≤ 2 ^ (22951 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 16001. -/
theorem theta15058_psi_16001_bounds :
    (16044277 : ℝ) / 1000 ≤ Chebyshev.psi 16001 ∧ Chebyshev.psi 16001 ≤ (16044971 : ℝ) / 1000 := by
  have hl : 2 ^ 23147 ≤ Nat.lcmUpto 16001 := by decide +kernel
  have hu : Nat.lcmUpto 16001 ≤ 2 ^ (23147 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 16139. -/
theorem theta15058_psi_16139_bounds :
    (16193997 : ℝ) / 1000 ≤ Chebyshev.psi 16139 ∧ Chebyshev.psi 16139 ≤ (16194691 : ℝ) / 1000 := by
  have hl : 2 ^ 23363 ≤ Nat.lcmUpto 16139 := by decide +kernel
  have hu : Nat.lcmUpto 16139 ≤ 2 ^ (23363 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 16141. -/
theorem theta15058_psi_16141_bounds :
    (16203701 : ℝ) / 1000 ≤ Chebyshev.psi 16141 ∧ Chebyshev.psi 16141 ≤ (16204395 : ℝ) / 1000 := by
  have hl : 2 ^ 23377 ≤ Nat.lcmUpto 16141 := by decide +kernel
  have hu : Nat.lcmUpto 16141 ≤ 2 ^ (23377 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 16273. -/
theorem theta15058_psi_16273_bounds :
    (16320150 : ℝ) / 1000 ≤ Chebyshev.psi 16273 ∧ Chebyshev.psi 16273 ≤ (16320844 : ℝ) / 1000 := by
  have hl : 2 ^ 23545 ≤ Nat.lcmUpto 16273 := by decide +kernel
  have hu : Nat.lcmUpto 16273 ≤ 2 ^ (23545 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 16381. -/
theorem theta15058_psi_16381_bounds :
    (16407486 : ℝ) / 1000 ≤ Chebyshev.psi 16381 ∧ Chebyshev.psi 16381 ≤ (16408181 : ℝ) / 1000 := by
  have hl : 2 ^ 23671 ≤ Nat.lcmUpto 16381 := by decide +kernel
  have hu : Nat.lcmUpto 16381 ≤ 2 ^ (23671 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- Every batch cell has a checked theta lower bound. -/
theorem theta15058_lower : ∀ r ∈ theta15058Cells, (r.lo : ℝ) / 1000 ≤ Chebyshev.theta r.a := by
  intro r hr
  simp only [theta15058Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change (14871450 : ℝ) / 1000 ≤ Chebyshev.theta (↑(15058 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 15058) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 15053) (b := 15058) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta15058_psi_15053_bounds.1]
  · change (14948389 : ℝ) / 1000 ≤ Chebyshev.theta (↑(15126 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 15126) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 15121) (b := 15126) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta15058_psi_15121_bounds.1]
  · change (15035033 : ℝ) / 1000 ≤ Chebyshev.theta (↑(15203 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 15203) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 15199) (b := 15203) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta15058_psi_15199_bounds.1]
  · change (15140391 : ℝ) / 1000 ≤ Chebyshev.theta (↑(15290 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 15290) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 15289) (b := 15290) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta15058_psi_15289_bounds.1]
  · change (15265851 : ℝ) / 1000 ≤ Chebyshev.theta (↑(15395 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 15395) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 15391) (b := 15395) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta15058_psi_15391_bounds.1]
  · change (15381606 : ℝ) / 1000 ≤ Chebyshev.theta (↑(15520 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 15520) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 15511) (b := 15520) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta15058_psi_15511_bounds.1]
  · change (15489737 : ℝ) / 1000 ≤ Chebyshev.theta (↑(15636 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 15636) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 15629) (b := 15636) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta15058_psi_15629_bounds.1]
  · change (15624901 : ℝ) / 1000 ≤ Chebyshev.theta (↑(15744 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 15744) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 15739) (b := 15744) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta15058_psi_15739_bounds.1]
  · change (15750360 : ℝ) / 1000 ≤ Chebyshev.theta (↑(15879 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 15879) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 15877) (b := 15879) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta15058_psi_15877_bounds.1]
  · change (15886217 : ℝ) / 1000 ≤ Chebyshev.theta (↑(16005 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 16005) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 16001) (b := 16005) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta15058_psi_16001_bounds.1]
  · change (16045641 : ℝ) / 1000 ≤ Chebyshev.theta (↑(16141 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 16141) (by norm_num only) (by norm_num only)
    linarith only [hd, theta15058_psi_16141_bounds.1]
  · change (16162090 : ℝ) / 1000 ≤ Chebyshev.theta (↑(16300 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 16300) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 16273) (b := 16300) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta15058_psi_16273_bounds.1]

/-- Every batch cell has a checked theta upper bound. -/
theorem theta15058_upper :
    ∀ r ∈ theta15058Cells, Chebyshev.theta (r.b - 1 : ℕ) ≤ (r.hi : ℝ) / 1000 := by
  intro r hr
  simp only [theta15058Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change Chebyshev.theta (↑(15125 : ℕ) : ℝ) ≤ (15107143 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 15125
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 15121) (b := 15125) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta15058_psi_15121_bounds.2]
  · change Chebyshev.theta (↑(15202 : ℕ) : ℝ) ≤ (15193787 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 15202
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 15199) (b := 15202) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta15058_psi_15199_bounds.2]
  · change Chebyshev.theta (↑(15289 : ℕ) : ℝ) ≤ (15299145 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 15289
    linarith only [hd, theta15058_psi_15289_bounds.2]
  · change Chebyshev.theta (↑(15394 : ℕ) : ℝ) ≤ (15424605 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 15394
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 15391) (b := 15394) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta15058_psi_15391_bounds.2]
  · change Chebyshev.theta (↑(15519 : ℕ) : ℝ) ≤ (15540360 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 15519
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 15511) (b := 15519) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta15058_psi_15511_bounds.2]
  · change Chebyshev.theta (↑(15635 : ℕ) : ℝ) ≤ (15648491 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 15635
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 15629) (b := 15635) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta15058_psi_15629_bounds.2]
  · change Chebyshev.theta (↑(15743 : ℕ) : ℝ) ≤ (15783655 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 15743
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 15739) (b := 15743) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta15058_psi_15739_bounds.2]
  · change Chebyshev.theta (↑(15878 : ℕ) : ℝ) ≤ (15909115 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 15878
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 15877) (b := 15878) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta15058_psi_15877_bounds.2]
  · change Chebyshev.theta (↑(16004 : ℕ) : ℝ) ≤ (16044971 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 16004
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 16001) (b := 16004) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta15058_psi_16001_bounds.2]
  · change Chebyshev.theta (↑(16140 : ℕ) : ℝ) ≤ (16194691 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 16140
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 16139) (b := 16140) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta15058_psi_16139_bounds.2]
  · change Chebyshev.theta (↑(16299 : ℕ) : ℝ) ≤ (16320844 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 16299
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 16273) (b := 16299) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta15058_psi_16273_bounds.2]
  · change Chebyshev.theta (↑(16383 : ℕ) : ℝ) ≤ (16408181 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 16383
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 16381) (b := 16383) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta15058_psi_16381_bounds.2]

/-- The envelope bound applies at every cell a endpoint. -/
theorem theta15058_a :
    ∀ r ∈ theta15058Cells,
      (r.ca : ℝ) / 1000 ≤
        Real.sqrt r.a *
          (Real.log r.a * (Real.log r.a - Real.log (Real.log r.a)) / (8 * Real.pi)) := by
  intro r hr
  simp only [theta15058Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 15058 *
          (Real.log 15058 * (Real.log 15058 - Real.log (Real.log 15058)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 15126 *
          (Real.log 15126 * (Real.log 15126 - Real.log (Real.log 15126)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 15203 *
          (Real.log 15203 * (Real.log 15203 - Real.log (Real.log 15203)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 15290 *
          (Real.log 15290 * (Real.log 15290 - Real.log (Real.log 15290)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 15395 *
          (Real.log 15395 * (Real.log 15395 - Real.log (Real.log 15395)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 15520 *
          (Real.log 15520 * (Real.log 15520 - Real.log (Real.log 15520)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 15636 *
          (Real.log 15636 * (Real.log 15636 - Real.log (Real.log 15636)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 15744 *
          (Real.log 15744 * (Real.log 15744 - Real.log (Real.log 15744)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 15879 *
          (Real.log 15879 * (Real.log 15879 - Real.log (Real.log 15879)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 16005 *
          (Real.log 16005 * (Real.log 16005 - Real.log (Real.log 16005)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 16141 *
          (Real.log 16141 * (Real.log 16141 - Real.log (Real.log 16141)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 16300 *
          (Real.log 16300 * (Real.log 16300 - Real.log (Real.log 16300)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)

/-- The envelope bound applies at every cell b endpoint. -/
theorem theta15058_b :
    ∀ r ∈ theta15058Cells,
      (r.cb : ℝ) / 1000 ≤
        Real.sqrt r.b *
          (Real.log r.b * (Real.log r.b - Real.log (Real.log r.b)) / (8 * Real.pi)) := by
  intro r hr
  simp only [theta15058Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 15126 *
          (Real.log 15126 * (Real.log 15126 - Real.log (Real.log 15126)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 15203 *
          (Real.log 15203 * (Real.log 15203 - Real.log (Real.log 15203)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 15290 *
          (Real.log 15290 * (Real.log 15290 - Real.log (Real.log 15290)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 15395 *
          (Real.log 15395 * (Real.log 15395 - Real.log (Real.log 15395)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 15520 *
          (Real.log 15520 * (Real.log 15520 - Real.log (Real.log 15520)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 15636 *
          (Real.log 15636 * (Real.log 15636 - Real.log (Real.log 15636)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 15744 *
          (Real.log 15744 * (Real.log 15744 - Real.log (Real.log 15744)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 15879 *
          (Real.log 15879 * (Real.log 15879 - Real.log (Real.log 15879)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 16005 *
          (Real.log 16005 * (Real.log 16005 - Real.log (Real.log 16005)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 16141 *
          (Real.log 16141 * (Real.log 16141 - Real.log (Real.log 16141)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 16300 *
          (Real.log 16300 * (Real.log 16300 - Real.log (Real.log 16300)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 16384 *
          (Real.log 16384 * (Real.log 16384 - Real.log (Real.log 16384)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)

/-- The cells form a checked chain covering `[15058, 16384)`. -/
theorem theta15058_check : leeNosalChainCheck 15058 16384 theta15058Cells = true := by
  decide +kernel

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
