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
def theta26035Cells : List LeeNosalCell :=
  [⟨26035, 26178, 25813466, 26171852, 365000, 365000⟩,
    ⟨26178, 26310, 25945858, 26313947, 365000, 365000⟩,
    ⟨26310, 26452, 26087953, 26466439, 365000, 365000⟩,
    ⟨26452, 26605, 26240445, 26593978, 365000, 365000⟩,
    ⟨26605, 26732, 26367984, 26767265, 365000, 365000⟩,
    ⟨26732, 26906, 26541271, 26940552, 365000, 365000⟩,
    ⟨26906, 27079, 26714558, 27124236, 365000, 365000⟩,
    ⟨27079, 27263, 26898242, 27267024, 365000, 365000⟩,
    ⟨27263, 27406, 27041030, 27369610, 365000, 365000⟩,
    ⟨27406, 27508, 27143616, 27471503, 365000, 365000⟩,
    ⟨27508, 27610, 27245509, 27553294, 365000, 365000⟩,
    ⟨27610, 27692, 27327300, 27635085, 365000, 365000⟩]

/-- The kernel-checked prefix bounds for 26029. -/
theorem theta26035_psi_26029_bounds :
    (26038766 : ℝ) / 1000 ≤ Chebyshev.psi 26029 ∧ Chebyshev.psi 26029 ≤ (26039461 : ℝ) / 1000 := by
  have hl : 2 ^ 37566 ≤ Nat.lcmUpto 26029 := by decide +kernel
  have hu : Nat.lcmUpto 26029 ≤ 2 ^ (37566 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 26177. -/
theorem theta26035_psi_26177_bounds :
    (26171158 : ℝ) / 1000 ≤ Chebyshev.psi 26177 ∧ Chebyshev.psi 26177 ≤ (26171852 : ℝ) / 1000 := by
  have hl : 2 ^ 37757 ≤ Nat.lcmUpto 26177 := by decide +kernel
  have hu : Nat.lcmUpto 26177 ≤ 2 ^ (37757 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 26309. -/
theorem theta26035_psi_26309_bounds :
    (26313253 : ℝ) / 1000 ≤ Chebyshev.psi 26309 ∧ Chebyshev.psi 26309 ≤ (26313947 : ℝ) / 1000 := by
  have hl : 2 ^ 37962 ≤ Nat.lcmUpto 26309 := by decide +kernel
  have hu : Nat.lcmUpto 26309 ≤ 2 ^ (37962 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 26449. -/
theorem theta26035_psi_26449_bounds :
    (26465745 : ℝ) / 1000 ≤ Chebyshev.psi 26449 ∧ Chebyshev.psi 26449 ≤ (26466439 : ℝ) / 1000 := by
  have hl : 2 ^ 38182 ≤ Nat.lcmUpto 26449 := by decide +kernel
  have hu : Nat.lcmUpto 26449 ≤ 2 ^ (38182 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 26597. -/
theorem theta26035_psi_26597_bounds :
    (26593284 : ℝ) / 1000 ≤ Chebyshev.psi 26597 ∧ Chebyshev.psi 26597 ≤ (26593978 : ℝ) / 1000 := by
  have hl : 2 ^ 38366 ≤ Nat.lcmUpto 26597 := by decide +kernel
  have hu : Nat.lcmUpto 26597 ≤ 2 ^ (38366 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 26731. -/
theorem theta26035_psi_26731_bounds :
    (26766571 : ℝ) / 1000 ≤ Chebyshev.psi 26731 ∧ Chebyshev.psi 26731 ≤ (26767265 : ℝ) / 1000 := by
  have hl : 2 ^ 38616 ≤ Nat.lcmUpto 26731 := by decide +kernel
  have hu : Nat.lcmUpto 26731 ≤ 2 ^ (38616 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 26903. -/
theorem theta26035_psi_26903_bounds :
    (26939858 : ℝ) / 1000 ≤ Chebyshev.psi 26903 ∧ Chebyshev.psi 26903 ≤ (26940552 : ℝ) / 1000 := by
  have hl : 2 ^ 38866 ≤ Nat.lcmUpto 26903 := by decide +kernel
  have hu : Nat.lcmUpto 26903 ≤ 2 ^ (38866 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 27077. -/
theorem theta26035_psi_27077_bounds :
    (27123542 : ℝ) / 1000 ≤ Chebyshev.psi 27077 ∧ Chebyshev.psi 27077 ≤ (27124236 : ℝ) / 1000 := by
  have hl : 2 ^ 39131 ≤ Nat.lcmUpto 27077 := by decide +kernel
  have hu : Nat.lcmUpto 27077 ≤ 2 ^ (39131 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 27259. -/
theorem theta26035_psi_27259_bounds :
    (27266330 : ℝ) / 1000 ≤ Chebyshev.psi 27259 ∧ Chebyshev.psi 27259 ≤ (27267024 : ℝ) / 1000 := by
  have hl : 2 ^ 39337 ≤ Nat.lcmUpto 27259 := by decide +kernel
  have hu : Nat.lcmUpto 27259 ≤ 2 ^ (39337 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 27397. -/
theorem theta26035_psi_27397_bounds :
    (27368916 : ℝ) / 1000 ≤ Chebyshev.psi 27397 ∧ Chebyshev.psi 27397 ≤ (27369610 : ℝ) / 1000 := by
  have hl : 2 ^ 39485 ≤ Nat.lcmUpto 27397 := by decide +kernel
  have hu : Nat.lcmUpto 27397 ≤ 2 ^ (39485 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 27487. -/
theorem theta26035_psi_27487_bounds :
    (27470809 : ℝ) / 1000 ≤ Chebyshev.psi 27487 ∧ Chebyshev.psi 27487 ≤ (27471503 : ℝ) / 1000 := by
  have hl : 2 ^ 39632 ≤ Nat.lcmUpto 27487 := by decide +kernel
  have hu : Nat.lcmUpto 27487 ≤ 2 ^ (39632 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 27583. -/
theorem theta26035_psi_27583_bounds :
    (27552600 : ℝ) / 1000 ≤ Chebyshev.psi 27583 ∧ Chebyshev.psi 27583 ≤ (27553294 : ℝ) / 1000 := by
  have hl : 2 ^ 39750 ≤ Nat.lcmUpto 27583 := by decide +kernel
  have hu : Nat.lcmUpto 27583 ≤ 2 ^ (39750 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 27691. -/
theorem theta26035_psi_27691_bounds :
    (27634391 : ℝ) / 1000 ≤ Chebyshev.psi 27691 ∧ Chebyshev.psi 27691 ≤ (27635085 : ℝ) / 1000 := by
  have hl : 2 ^ 39868 ≤ Nat.lcmUpto 27691 := by decide +kernel
  have hu : Nat.lcmUpto 27691 ≤ 2 ^ (39868 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- Every batch cell has a checked theta lower bound. -/
theorem theta26035_lower : ∀ r ∈ theta26035Cells, (r.lo : ℝ) / 1000 ≤ Chebyshev.theta r.a := by
  intro r hr
  simp only [theta26035Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change (25813466 : ℝ) / 1000 ≤ Chebyshev.theta (↑(26035 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 26035) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 26029) (b := 26035) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta26035_psi_26029_bounds.1]
  · change (25945858 : ℝ) / 1000 ≤ Chebyshev.theta (↑(26178 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 26178) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 26177) (b := 26178) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta26035_psi_26177_bounds.1]
  · change (26087953 : ℝ) / 1000 ≤ Chebyshev.theta (↑(26310 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 26310) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 26309) (b := 26310) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta26035_psi_26309_bounds.1]
  · change (26240445 : ℝ) / 1000 ≤ Chebyshev.theta (↑(26452 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 26452) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 26449) (b := 26452) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta26035_psi_26449_bounds.1]
  · change (26367984 : ℝ) / 1000 ≤ Chebyshev.theta (↑(26605 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 26605) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 26597) (b := 26605) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta26035_psi_26597_bounds.1]
  · change (26541271 : ℝ) / 1000 ≤ Chebyshev.theta (↑(26732 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 26732) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 26731) (b := 26732) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta26035_psi_26731_bounds.1]
  · change (26714558 : ℝ) / 1000 ≤ Chebyshev.theta (↑(26906 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 26906) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 26903) (b := 26906) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta26035_psi_26903_bounds.1]
  · change (26898242 : ℝ) / 1000 ≤ Chebyshev.theta (↑(27079 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 27079) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 27077) (b := 27079) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta26035_psi_27077_bounds.1]
  · change (27041030 : ℝ) / 1000 ≤ Chebyshev.theta (↑(27263 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 27263) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 27259) (b := 27263) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta26035_psi_27259_bounds.1]
  · change (27143616 : ℝ) / 1000 ≤ Chebyshev.theta (↑(27406 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 27406) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 27397) (b := 27406) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta26035_psi_27397_bounds.1]
  · change (27245509 : ℝ) / 1000 ≤ Chebyshev.theta (↑(27508 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 27508) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 27487) (b := 27508) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta26035_psi_27487_bounds.1]
  · change (27327300 : ℝ) / 1000 ≤ Chebyshev.theta (↑(27610 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 27610) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 27583) (b := 27610) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta26035_psi_27583_bounds.1]

/-- Every batch cell has a checked theta upper bound. -/
theorem theta26035_upper :
    ∀ r ∈ theta26035Cells, Chebyshev.theta (r.b - 1 : ℕ) ≤ (r.hi : ℝ) / 1000 := by
  intro r hr
  simp only [theta26035Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change Chebyshev.theta (↑(26177 : ℕ) : ℝ) ≤ (26171852 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 26177
    linarith only [hd, theta26035_psi_26177_bounds.2]
  · change Chebyshev.theta (↑(26309 : ℕ) : ℝ) ≤ (26313947 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 26309
    linarith only [hd, theta26035_psi_26309_bounds.2]
  · change Chebyshev.theta (↑(26451 : ℕ) : ℝ) ≤ (26466439 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 26451
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 26449) (b := 26451) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta26035_psi_26449_bounds.2]
  · change Chebyshev.theta (↑(26604 : ℕ) : ℝ) ≤ (26593978 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 26604
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 26597) (b := 26604) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta26035_psi_26597_bounds.2]
  · change Chebyshev.theta (↑(26731 : ℕ) : ℝ) ≤ (26767265 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 26731
    linarith only [hd, theta26035_psi_26731_bounds.2]
  · change Chebyshev.theta (↑(26905 : ℕ) : ℝ) ≤ (26940552 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 26905
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 26903) (b := 26905) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta26035_psi_26903_bounds.2]
  · change Chebyshev.theta (↑(27078 : ℕ) : ℝ) ≤ (27124236 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 27078
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 27077) (b := 27078) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta26035_psi_27077_bounds.2]
  · change Chebyshev.theta (↑(27262 : ℕ) : ℝ) ≤ (27267024 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 27262
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 27259) (b := 27262) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta26035_psi_27259_bounds.2]
  · change Chebyshev.theta (↑(27405 : ℕ) : ℝ) ≤ (27369610 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 27405
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 27397) (b := 27405) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta26035_psi_27397_bounds.2]
  · change Chebyshev.theta (↑(27507 : ℕ) : ℝ) ≤ (27471503 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 27507
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 27487) (b := 27507) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta26035_psi_27487_bounds.2]
  · change Chebyshev.theta (↑(27609 : ℕ) : ℝ) ≤ (27553294 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 27609
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 27583) (b := 27609) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta26035_psi_27583_bounds.2]
  · change Chebyshev.theta (↑(27691 : ℕ) : ℝ) ≤ (27635085 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 27691
    linarith only [hd, theta26035_psi_27691_bounds.2]

/-- The envelope bound applies at every cell a endpoint. -/
theorem theta26035_a :
    ∀ r ∈ theta26035Cells,
      (r.ca : ℝ) / 1000 ≤
        Real.sqrt r.a *
          (Real.log r.a * (Real.log r.a - Real.log (Real.log r.a)) / (8 * Real.pi)) := by
  intro r hr
  simp only [theta26035Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 26035 *
          (Real.log 26035 * (Real.log 26035 - Real.log (Real.log 26035)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 26178 *
          (Real.log 26178 * (Real.log 26178 - Real.log (Real.log 26178)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 26310 *
          (Real.log 26310 * (Real.log 26310 - Real.log (Real.log 26310)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 26452 *
          (Real.log 26452 * (Real.log 26452 - Real.log (Real.log 26452)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 26605 *
          (Real.log 26605 * (Real.log 26605 - Real.log (Real.log 26605)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 26732 *
          (Real.log 26732 * (Real.log 26732 - Real.log (Real.log 26732)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 26906 *
          (Real.log 26906 * (Real.log 26906 - Real.log (Real.log 26906)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 27079 *
          (Real.log 27079 * (Real.log 27079 - Real.log (Real.log 27079)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 27263 *
          (Real.log 27263 * (Real.log 27263 - Real.log (Real.log 27263)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 27406 *
          (Real.log 27406 * (Real.log 27406 - Real.log (Real.log 27406)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 27508 *
          (Real.log 27508 * (Real.log 27508 - Real.log (Real.log 27508)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 27610 *
          (Real.log 27610 * (Real.log 27610 - Real.log (Real.log 27610)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)

/-- The envelope bound applies at every cell b endpoint. -/
theorem theta26035_b :
    ∀ r ∈ theta26035Cells,
      (r.cb : ℝ) / 1000 ≤
        Real.sqrt r.b *
          (Real.log r.b * (Real.log r.b - Real.log (Real.log r.b)) / (8 * Real.pi)) := by
  intro r hr
  simp only [theta26035Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 26178 *
          (Real.log 26178 * (Real.log 26178 - Real.log (Real.log 26178)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 26310 *
          (Real.log 26310 * (Real.log 26310 - Real.log (Real.log 26310)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 26452 *
          (Real.log 26452 * (Real.log 26452 - Real.log (Real.log 26452)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 26605 *
          (Real.log 26605 * (Real.log 26605 - Real.log (Real.log 26605)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 26732 *
          (Real.log 26732 * (Real.log 26732 - Real.log (Real.log 26732)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 26906 *
          (Real.log 26906 * (Real.log 26906 - Real.log (Real.log 26906)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 27079 *
          (Real.log 27079 * (Real.log 27079 - Real.log (Real.log 27079)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 27263 *
          (Real.log 27263 * (Real.log 27263 - Real.log (Real.log 27263)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 27406 *
          (Real.log 27406 * (Real.log 27406 - Real.log (Real.log 27406)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 27508 *
          (Real.log 27508 * (Real.log 27508 - Real.log (Real.log 27508)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 27610 *
          (Real.log 27610 * (Real.log 27610 - Real.log (Real.log 27610)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 27692 *
          (Real.log 27692 * (Real.log 27692 - Real.log (Real.log 27692)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)

/-- The cells form a checked chain covering `[26035, 27692)`. -/
theorem theta26035_check : leeNosalChainCheck 26035 27692 theta26035Cells = true := by
  decide +kernel

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
