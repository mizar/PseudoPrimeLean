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
def theta10000Cells : List LeeNosalCell :=
  [⟨10000, 10110, 9855144, 10124108, 255000, 255000⟩,
    ⟨10110, 10220, 9965354, 10239864, 255000, 255000⟩,
    ⟨10220, 10336, 10081110, 10378493, 255000, 255000⟩,
    ⟨10336, 10474, 10219739, 10498408, 255000, 255000⟩,
    ⟨10474, 10594, 10339654, 10591289, 255000, 255000⟩,
    ⟨10594, 10687, 10432535, 10698034, 255000, 255000⟩,
    ⟨10687, 10803, 10548291, 10818642, 255000, 255000⟩,
    ⟨10803, 10914, 10659888, 10930238, 255000, 255000⟩,
    ⟨10914, 11026, 10771484, 11013416, 255000, 255000⟩,
    ⟨11026, 11109, 10854662, 11097287, 255000, 255000⟩,
    ⟨11109, 11193, 10938533, 11190862, 255000, 255000⟩,
    ⟨11193, 11287, 11032108, 11274733, 255000, 255000⟩]

/-- The kernel-checked prefix bounds for 9973. -/
theorem theta10000_psi_9973_bounds :
    (10013204 : ℝ) / 1000 ≤ Chebyshev.psi 9973 ∧ Chebyshev.psi 9973 ≤ (10013898 : ℝ) / 1000 := by
  have hl : 2 ^ 14446 ≤ Nat.lcmUpto 9973 := by decide +kernel
  have hu : Nat.lcmUpto 9973 ≤ 2 ^ (14446 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 10103. -/
theorem theta10000_psi_10103_bounds :
    (10123414 : ℝ) / 1000 ≤ Chebyshev.psi 10103 ∧ Chebyshev.psi 10103 ≤ (10124108 : ℝ) / 1000 := by
  have hl : 2 ^ 14605 ≤ Nat.lcmUpto 10103 := by decide +kernel
  have hu : Nat.lcmUpto 10103 ≤ 2 ^ (14605 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 10211. -/
theorem theta10000_psi_10211_bounds :
    (10239170 : ℝ) / 1000 ≤ Chebyshev.psi 10211 ∧ Chebyshev.psi 10211 ≤ (10239864 : ℝ) / 1000 := by
  have hl : 2 ^ 14772 ≤ Nat.lcmUpto 10211 := by decide +kernel
  have hu : Nat.lcmUpto 10211 ≤ 2 ^ (14772 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 10333. -/
theorem theta10000_psi_10333_bounds :
    (10377799 : ℝ) / 1000 ≤ Chebyshev.psi 10333 ∧ Chebyshev.psi 10333 ≤ (10378493 : ℝ) / 1000 := by
  have hl : 2 ^ 14972 ≤ Nat.lcmUpto 10333 := by decide +kernel
  have hu : Nat.lcmUpto 10333 ≤ 2 ^ (14972 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 10463. -/
theorem theta10000_psi_10463_bounds :
    (10497714 : ℝ) / 1000 ≤ Chebyshev.psi 10463 ∧ Chebyshev.psi 10463 ≤ (10498408 : ℝ) / 1000 := by
  have hl : 2 ^ 15145 ≤ Nat.lcmUpto 10463 := by decide +kernel
  have hu : Nat.lcmUpto 10463 ≤ 2 ^ (15145 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 10589. -/
theorem theta10000_psi_10589_bounds :
    (10590595 : ℝ) / 1000 ≤ Chebyshev.psi 10589 ∧ Chebyshev.psi 10589 ≤ (10591289 : ℝ) / 1000 := by
  have hl : 2 ^ 15279 ≤ Nat.lcmUpto 10589 := by decide +kernel
  have hu : Nat.lcmUpto 10589 ≤ 2 ^ (15279 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 10667. -/
theorem theta10000_psi_10667_bounds :
    (10697340 : ℝ) / 1000 ≤ Chebyshev.psi 10667 ∧ Chebyshev.psi 10667 ≤ (10698034 : ℝ) / 1000 := by
  have hl : 2 ^ 15433 ≤ Nat.lcmUpto 10667 := by decide +kernel
  have hu : Nat.lcmUpto 10667 ≤ 2 ^ (15433 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 10687. -/
theorem theta10000_psi_10687_bounds :
    (10706351 : ℝ) / 1000 ≤ Chebyshev.psi 10687 ∧ Chebyshev.psi 10687 ≤ (10707045 : ℝ) / 1000 := by
  have hl : 2 ^ 15446 ≤ Nat.lcmUpto 10687 := by decide +kernel
  have hu : Nat.lcmUpto 10687 ≤ 2 ^ (15446 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 10799. -/
theorem theta10000_psi_10799_bounds :
    (10817948 : ℝ) / 1000 ≤ Chebyshev.psi 10799 ∧ Chebyshev.psi 10799 ≤ (10818642 : ℝ) / 1000 := by
  have hl : 2 ^ 15607 ≤ Nat.lcmUpto 10799 := by decide +kernel
  have hu : Nat.lcmUpto 10799 ≤ 2 ^ (15607 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 10909. -/
theorem theta10000_psi_10909_bounds :
    (10929544 : ℝ) / 1000 ≤ Chebyshev.psi 10909 ∧ Chebyshev.psi 10909 ≤ (10930238 : ℝ) / 1000 := by
  have hl : 2 ^ 15768 ≤ Nat.lcmUpto 10909 := by decide +kernel
  have hu : Nat.lcmUpto 10909 ≤ 2 ^ (15768 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 11003. -/
theorem theta10000_psi_11003_bounds :
    (11012722 : ℝ) / 1000 ≤ Chebyshev.psi 11003 ∧ Chebyshev.psi 11003 ≤ (11013416 : ℝ) / 1000 := by
  have hl : 2 ^ 15888 ≤ Nat.lcmUpto 11003 := by decide +kernel
  have hu : Nat.lcmUpto 11003 ≤ 2 ^ (15888 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 11093. -/
theorem theta10000_psi_11093_bounds :
    (11096593 : ℝ) / 1000 ≤ Chebyshev.psi 11093 ∧ Chebyshev.psi 11093 ≤ (11097287 : ℝ) / 1000 := by
  have hl : 2 ^ 16009 ≤ Nat.lcmUpto 11093 := by decide +kernel
  have hu : Nat.lcmUpto 11093 ≤ 2 ^ (16009 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 11177. -/
theorem theta10000_psi_11177_bounds :
    (11190168 : ℝ) / 1000 ≤ Chebyshev.psi 11177 ∧ Chebyshev.psi 11177 ≤ (11190862 : ℝ) / 1000 := by
  have hl : 2 ^ 16144 ≤ Nat.lcmUpto 11177 := by decide +kernel
  have hu : Nat.lcmUpto 11177 ≤ 2 ^ (16144 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 11279. -/
theorem theta10000_psi_11279_bounds :
    (11274038 : ℝ) / 1000 ≤ Chebyshev.psi 11279 ∧ Chebyshev.psi 11279 ≤ (11274733 : ℝ) / 1000 := by
  have hl : 2 ^ 16265 ≤ Nat.lcmUpto 11279 := by decide +kernel
  have hu : Nat.lcmUpto 11279 ≤ 2 ^ (16265 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- Every batch cell has a checked theta lower bound. -/
theorem theta10000_lower : ∀ r ∈ theta10000Cells, (r.lo : ℝ) / 1000 ≤ Chebyshev.theta r.a := by
  intro r hr
  simp only [theta10000Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change (9855144 : ℝ) / 1000 ≤ Chebyshev.theta (↑(10000 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 10000) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 9973) (b := 10000) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta10000_psi_9973_bounds.1]
  · change (9965354 : ℝ) / 1000 ≤ Chebyshev.theta (↑(10110 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 10110) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 10103) (b := 10110) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta10000_psi_10103_bounds.1]
  · change (10081110 : ℝ) / 1000 ≤ Chebyshev.theta (↑(10220 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 10220) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 10211) (b := 10220) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta10000_psi_10211_bounds.1]
  · change (10219739 : ℝ) / 1000 ≤ Chebyshev.theta (↑(10336 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 10336) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 10333) (b := 10336) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta10000_psi_10333_bounds.1]
  · change (10339654 : ℝ) / 1000 ≤ Chebyshev.theta (↑(10474 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 10474) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 10463) (b := 10474) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta10000_psi_10463_bounds.1]
  · change (10432535 : ℝ) / 1000 ≤ Chebyshev.theta (↑(10594 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 10594) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 10589) (b := 10594) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta10000_psi_10589_bounds.1]
  · change (10548291 : ℝ) / 1000 ≤ Chebyshev.theta (↑(10687 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 10687) (by norm_num only) (by norm_num only)
    linarith only [hd, theta10000_psi_10687_bounds.1]
  · change (10659888 : ℝ) / 1000 ≤ Chebyshev.theta (↑(10803 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 10803) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 10799) (b := 10803) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta10000_psi_10799_bounds.1]
  · change (10771484 : ℝ) / 1000 ≤ Chebyshev.theta (↑(10914 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 10914) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 10909) (b := 10914) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta10000_psi_10909_bounds.1]
  · change (10854662 : ℝ) / 1000 ≤ Chebyshev.theta (↑(11026 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 11026) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 11003) (b := 11026) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta10000_psi_11003_bounds.1]
  · change (10938533 : ℝ) / 1000 ≤ Chebyshev.theta (↑(11109 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 11109) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 11093) (b := 11109) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta10000_psi_11093_bounds.1]
  · change (11032108 : ℝ) / 1000 ≤ Chebyshev.theta (↑(11193 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 11193) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 11177) (b := 11193) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta10000_psi_11177_bounds.1]

/-- Every batch cell has a checked theta upper bound. -/
theorem theta10000_upper :
    ∀ r ∈ theta10000Cells, Chebyshev.theta (r.b - 1 : ℕ) ≤ (r.hi : ℝ) / 1000 := by
  intro r hr
  simp only [theta10000Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change Chebyshev.theta (↑(10109 : ℕ) : ℝ) ≤ (10124108 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 10109
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 10103) (b := 10109) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta10000_psi_10103_bounds.2]
  · change Chebyshev.theta (↑(10219 : ℕ) : ℝ) ≤ (10239864 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 10219
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 10211) (b := 10219) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta10000_psi_10211_bounds.2]
  · change Chebyshev.theta (↑(10335 : ℕ) : ℝ) ≤ (10378493 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 10335
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 10333) (b := 10335) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta10000_psi_10333_bounds.2]
  · change Chebyshev.theta (↑(10473 : ℕ) : ℝ) ≤ (10498408 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 10473
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 10463) (b := 10473) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta10000_psi_10463_bounds.2]
  · change Chebyshev.theta (↑(10593 : ℕ) : ℝ) ≤ (10591289 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 10593
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 10589) (b := 10593) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta10000_psi_10589_bounds.2]
  · change Chebyshev.theta (↑(10686 : ℕ) : ℝ) ≤ (10698034 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 10686
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 10667) (b := 10686) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta10000_psi_10667_bounds.2]
  · change Chebyshev.theta (↑(10802 : ℕ) : ℝ) ≤ (10818642 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 10802
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 10799) (b := 10802) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta10000_psi_10799_bounds.2]
  · change Chebyshev.theta (↑(10913 : ℕ) : ℝ) ≤ (10930238 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 10913
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 10909) (b := 10913) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta10000_psi_10909_bounds.2]
  · change Chebyshev.theta (↑(11025 : ℕ) : ℝ) ≤ (11013416 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 11025
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 11003) (b := 11025) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta10000_psi_11003_bounds.2]
  · change Chebyshev.theta (↑(11108 : ℕ) : ℝ) ≤ (11097287 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 11108
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 11093) (b := 11108) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta10000_psi_11093_bounds.2]
  · change Chebyshev.theta (↑(11192 : ℕ) : ℝ) ≤ (11190862 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 11192
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 11177) (b := 11192) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta10000_psi_11177_bounds.2]
  · change Chebyshev.theta (↑(11286 : ℕ) : ℝ) ≤ (11274733 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 11286
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 11279) (b := 11286) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta10000_psi_11279_bounds.2]

/-- The envelope bound applies at every cell a endpoint. -/
theorem theta10000_a :
    ∀ r ∈ theta10000Cells,
      (r.ca : ℝ) / 1000 ≤
        Real.sqrt r.a *
          (Real.log r.a * (Real.log r.a - Real.log (Real.log r.a)) / (8 * Real.pi)) := by
  intro r hr
  simp only [theta10000Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 10000 *
          (Real.log 10000 * (Real.log 10000 - Real.log (Real.log 10000)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 10110 *
          (Real.log 10110 * (Real.log 10110 - Real.log (Real.log 10110)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 10220 *
          (Real.log 10220 * (Real.log 10220 - Real.log (Real.log 10220)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 10336 *
          (Real.log 10336 * (Real.log 10336 - Real.log (Real.log 10336)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 10474 *
          (Real.log 10474 * (Real.log 10474 - Real.log (Real.log 10474)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 10594 *
          (Real.log 10594 * (Real.log 10594 - Real.log (Real.log 10594)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 10687 *
          (Real.log 10687 * (Real.log 10687 - Real.log (Real.log 10687)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 10803 *
          (Real.log 10803 * (Real.log 10803 - Real.log (Real.log 10803)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 10914 *
          (Real.log 10914 * (Real.log 10914 - Real.log (Real.log 10914)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 11026 *
          (Real.log 11026 * (Real.log 11026 - Real.log (Real.log 11026)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 11109 *
          (Real.log 11109 * (Real.log 11109 - Real.log (Real.log 11109)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 11193 *
          (Real.log 11193 * (Real.log 11193 - Real.log (Real.log 11193)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)

/-- The envelope bound applies at every cell b endpoint. -/
theorem theta10000_b :
    ∀ r ∈ theta10000Cells,
      (r.cb : ℝ) / 1000 ≤
        Real.sqrt r.b *
          (Real.log r.b * (Real.log r.b - Real.log (Real.log r.b)) / (8 * Real.pi)) := by
  intro r hr
  simp only [theta10000Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 10110 *
          (Real.log 10110 * (Real.log 10110 - Real.log (Real.log 10110)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 10220 *
          (Real.log 10220 * (Real.log 10220 - Real.log (Real.log 10220)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 10336 *
          (Real.log 10336 * (Real.log 10336 - Real.log (Real.log 10336)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 10474 *
          (Real.log 10474 * (Real.log 10474 - Real.log (Real.log 10474)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 10594 *
          (Real.log 10594 * (Real.log 10594 - Real.log (Real.log 10594)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 10687 *
          (Real.log 10687 * (Real.log 10687 - Real.log (Real.log 10687)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 10803 *
          (Real.log 10803 * (Real.log 10803 - Real.log (Real.log 10803)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 10914 *
          (Real.log 10914 * (Real.log 10914 - Real.log (Real.log 10914)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 11026 *
          (Real.log 11026 * (Real.log 11026 - Real.log (Real.log 11026)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 11109 *
          (Real.log 11109 * (Real.log 11109 - Real.log (Real.log 11109)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 11193 *
          (Real.log 11193 * (Real.log 11193 - Real.log (Real.log 11193)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 11287 *
          (Real.log 11287 * (Real.log 11287 - Real.log (Real.log 11287)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)

/-- The cells form a checked chain covering `[10000, 11287)`. -/
theorem theta10000_check : leeNosalChainCheck 10000 11287 theta10000Cells = true := by
  decide +kernel

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
