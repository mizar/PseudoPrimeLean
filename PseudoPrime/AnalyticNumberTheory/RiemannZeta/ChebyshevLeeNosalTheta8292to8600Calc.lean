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
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalEnvelope7776
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalMonotone
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalChecker

/-! # Batch certificate for Lee–Nosal theta cells -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The local cells store endpoint bounds in thousandths. -/
def theta8292Cells : List LeeNosalCell :=
  [⟨8292, 8337, 8126435, 8330936, 211000, 211000⟩, ⟨8337, 8383, 8172182, 8366980, 211000, 211000⟩,
    ⟨8383, 8419, 8208226, 8385002, 211000, 211000⟩, ⟨8419, 8446, 8235259, 8430057, 211000, 211000⟩,
    ⟨8446, 8482, 8271302, 8457089, 211000, 211000⟩, ⟨8482, 8509, 8298335, 8466100, 211000, 211000⟩,
    ⟨8509, 8518, 8307346, 8475111, 211000, 211000⟩, ⟨8518, 8527, 8316357, 8484122, 211000, 211000⟩,
    ⟨8527, 8545, 8334379, 8520859, 211000, 211000⟩, ⟨8545, 8573, 8362105, 8529870, 211000, 211000⟩,
    ⟨8573, 8591, 8380126, 8547892, 211000, 211000⟩, ⟨8591, 8600, 8389137, 8565913, 211000, 211000⟩]

/-- The kernel-checked prefix bounds for 8291. -/
theorem theta8292_psi_8291_bounds :
    (8284495 : ℝ) / 1000 ≤ Chebyshev.psi 8291 ∧ Chebyshev.psi 8291 ≤ (8285189 : ℝ) / 1000 := by
  have hl : 2 ^ 11952 ≤ Nat.lcmUpto 8291 := by decide +kernel
  have hu : Nat.lcmUpto 8291 ≤ 2 ^ (11952 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 8329. -/
theorem theta8292_psi_8329_bounds :
    (8330242 : ℝ) / 1000 ≤ Chebyshev.psi 8329 ∧ Chebyshev.psi 8329 ≤ (8330936 : ℝ) / 1000 := by
  have hl : 2 ^ 12018 ≤ Nat.lcmUpto 8329 := by decide +kernel
  have hu : Nat.lcmUpto 8329 ≤ 2 ^ (12018 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 8377. -/
theorem theta8292_psi_8377_bounds :
    (8366286 : ℝ) / 1000 ≤ Chebyshev.psi 8377 ∧ Chebyshev.psi 8377 ≤ (8366980 : ℝ) / 1000 := by
  have hl : 2 ^ 12070 ≤ Nat.lcmUpto 8377 := by decide +kernel
  have hu : Nat.lcmUpto 8377 ≤ 2 ^ (12070 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 8389. -/
theorem theta8292_psi_8389_bounds :
    (8384308 : ℝ) / 1000 ≤ Chebyshev.psi 8389 ∧ Chebyshev.psi 8389 ≤ (8385002 : ℝ) / 1000 := by
  have hl : 2 ^ 12096 ≤ Nat.lcmUpto 8389 := by decide +kernel
  have hu : Nat.lcmUpto 8389 ≤ 2 ^ (12096 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 8419. -/
theorem theta8292_psi_8419_bounds :
    (8393319 : ℝ) / 1000 ≤ Chebyshev.psi 8419 ∧ Chebyshev.psi 8419 ≤ (8394013 : ℝ) / 1000 := by
  have hl : 2 ^ 12109 ≤ Nat.lcmUpto 8419 := by decide +kernel
  have hu : Nat.lcmUpto 8419 ≤ 2 ^ (12109 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 8443. -/
theorem theta8292_psi_8443_bounds :
    (8429362 : ℝ) / 1000 ≤ Chebyshev.psi 8443 ∧ Chebyshev.psi 8443 ≤ (8430057 : ℝ) / 1000 := by
  have hl : 2 ^ 12161 ≤ Nat.lcmUpto 8443 := by decide +kernel
  have hu : Nat.lcmUpto 8443 ≤ 2 ^ (12161 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 8467. -/
theorem theta8292_psi_8467_bounds :
    (8456395 : ℝ) / 1000 ≤ Chebyshev.psi 8467 ∧ Chebyshev.psi 8467 ≤ (8457089 : ℝ) / 1000 := by
  have hl : 2 ^ 12200 ≤ Nat.lcmUpto 8467 := by decide +kernel
  have hu : Nat.lcmUpto 8467 ≤ 2 ^ (12200 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 8501. -/
theorem theta8292_psi_8501_bounds :
    (8465406 : ℝ) / 1000 ≤ Chebyshev.psi 8501 ∧ Chebyshev.psi 8501 ≤ (8466100 : ℝ) / 1000 := by
  have hl : 2 ^ 12213 ≤ Nat.lcmUpto 8501 := by decide +kernel
  have hu : Nat.lcmUpto 8501 ≤ 2 ^ (12213 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 8513. -/
theorem theta8292_psi_8513_bounds :
    (8474417 : ℝ) / 1000 ≤ Chebyshev.psi 8513 ∧ Chebyshev.psi 8513 ≤ (8475111 : ℝ) / 1000 := by
  have hl : 2 ^ 12226 ≤ Nat.lcmUpto 8513 := by decide +kernel
  have hu : Nat.lcmUpto 8513 ≤ 2 ^ (12226 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 8521. -/
theorem theta8292_psi_8521_bounds :
    (8483428 : ℝ) / 1000 ≤ Chebyshev.psi 8521 ∧ Chebyshev.psi 8521 ≤ (8484122 : ℝ) / 1000 := by
  have hl : 2 ^ 12239 ≤ Nat.lcmUpto 8521 := by decide +kernel
  have hu : Nat.lcmUpto 8521 ≤ 2 ^ (12239 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 8527. -/
theorem theta8292_psi_8527_bounds :
    (8492439 : ℝ) / 1000 ≤ Chebyshev.psi 8527 ∧ Chebyshev.psi 8527 ≤ (8493133 : ℝ) / 1000 := by
  have hl : 2 ^ 12252 ≤ Nat.lcmUpto 8527 := by decide +kernel
  have hu : Nat.lcmUpto 8527 ≤ 2 ^ (12252 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 8543. -/
theorem theta8292_psi_8543_bounds :
    (8520165 : ℝ) / 1000 ≤ Chebyshev.psi 8543 ∧ Chebyshev.psi 8543 ≤ (8520859 : ℝ) / 1000 := by
  have hl : 2 ^ 12292 ≤ Nat.lcmUpto 8543 := by decide +kernel
  have hu : Nat.lcmUpto 8543 ≤ 2 ^ (12292 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 8563. -/
theorem theta8292_psi_8563_bounds :
    (8529176 : ℝ) / 1000 ≤ Chebyshev.psi 8563 ∧ Chebyshev.psi 8563 ≤ (8529870 : ℝ) / 1000 := by
  have hl : 2 ^ 12305 ≤ Nat.lcmUpto 8563 := by decide +kernel
  have hu : Nat.lcmUpto 8563 ≤ 2 ^ (12305 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 8573. -/
theorem theta8292_psi_8573_bounds :
    (8538186 : ℝ) / 1000 ≤ Chebyshev.psi 8573 ∧ Chebyshev.psi 8573 ≤ (8538881 : ℝ) / 1000 := by
  have hl : 2 ^ 12318 ≤ Nat.lcmUpto 8573 := by decide +kernel
  have hu : Nat.lcmUpto 8573 ≤ 2 ^ (12318 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 8581. -/
theorem theta8292_psi_8581_bounds :
    (8547197 : ℝ) / 1000 ≤ Chebyshev.psi 8581 ∧ Chebyshev.psi 8581 ≤ (8547892 : ℝ) / 1000 := by
  have hl : 2 ^ 12331 ≤ Nat.lcmUpto 8581 := by decide +kernel
  have hu : Nat.lcmUpto 8581 ≤ 2 ^ (12331 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 8599. -/
theorem theta8292_psi_8599_bounds :
    (8565219 : ℝ) / 1000 ≤ Chebyshev.psi 8599 ∧ Chebyshev.psi 8599 ≤ (8565913 : ℝ) / 1000 := by
  have hl : 2 ^ 12357 ≤ Nat.lcmUpto 8599 := by decide +kernel
  have hu : Nat.lcmUpto 8599 ≤ 2 ^ (12357 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- Every batch cell has a checked theta lower bound. -/
theorem theta8292_lower : ∀ r ∈ theta8292Cells, (r.lo : ℝ) / 1000 ≤ Chebyshev.theta r.a := by
  intro r hr
  simp only [theta8292Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change (8126435 : ℝ) / 1000 ≤ Chebyshev.theta (↑(8292 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 8292) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 8291) (b := 8292) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta8292_psi_8291_bounds.1]
  · change (8172182 : ℝ) / 1000 ≤ Chebyshev.theta (↑(8337 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 8337) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 8329) (b := 8337) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta8292_psi_8329_bounds.1]
  · change (8208226 : ℝ) / 1000 ≤ Chebyshev.theta (↑(8383 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 8383) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 8377) (b := 8383) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta8292_psi_8377_bounds.1]
  · change (8235259 : ℝ) / 1000 ≤ Chebyshev.theta (↑(8419 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 8419) (by norm_num only) (by norm_num only)
    linarith only [hd, theta8292_psi_8419_bounds.1]
  · change (8271302 : ℝ) / 1000 ≤ Chebyshev.theta (↑(8446 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 8446) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 8443) (b := 8446) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta8292_psi_8443_bounds.1]
  · change (8298335 : ℝ) / 1000 ≤ Chebyshev.theta (↑(8482 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 8482) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 8467) (b := 8482) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta8292_psi_8467_bounds.1]
  · change (8307346 : ℝ) / 1000 ≤ Chebyshev.theta (↑(8509 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 8509) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 8501) (b := 8509) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta8292_psi_8501_bounds.1]
  · change (8316357 : ℝ) / 1000 ≤ Chebyshev.theta (↑(8518 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 8518) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 8513) (b := 8518) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta8292_psi_8513_bounds.1]
  · change (8334379 : ℝ) / 1000 ≤ Chebyshev.theta (↑(8527 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 8527) (by norm_num only) (by norm_num only)
    linarith only [hd, theta8292_psi_8527_bounds.1]
  · change (8362105 : ℝ) / 1000 ≤ Chebyshev.theta (↑(8545 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 8545) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 8543) (b := 8545) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta8292_psi_8543_bounds.1]
  · change (8380126 : ℝ) / 1000 ≤ Chebyshev.theta (↑(8573 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 8573) (by norm_num only) (by norm_num only)
    linarith only [hd, theta8292_psi_8573_bounds.1]
  · change (8389137 : ℝ) / 1000 ≤ Chebyshev.theta (↑(8591 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 8591) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 8581) (b := 8591) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta8292_psi_8581_bounds.1]

/-- Every batch cell has a checked theta upper bound. -/
theorem theta8292_upper :
    ∀ r ∈ theta8292Cells, Chebyshev.theta (r.b - 1 : ℕ) ≤ (r.hi : ℝ) / 1000 := by
  intro r hr
  simp only [theta8292Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change Chebyshev.theta (↑(8336 : ℕ) : ℝ) ≤ (8330936 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 8336
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 8329) (b := 8336) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta8292_psi_8329_bounds.2]
  · change Chebyshev.theta (↑(8382 : ℕ) : ℝ) ≤ (8366980 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 8382
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 8377) (b := 8382) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta8292_psi_8377_bounds.2]
  · change Chebyshev.theta (↑(8418 : ℕ) : ℝ) ≤ (8385002 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 8418
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 8389) (b := 8418) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta8292_psi_8389_bounds.2]
  · change Chebyshev.theta (↑(8445 : ℕ) : ℝ) ≤ (8430057 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 8445
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 8443) (b := 8445) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta8292_psi_8443_bounds.2]
  · change Chebyshev.theta (↑(8481 : ℕ) : ℝ) ≤ (8457089 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 8481
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 8467) (b := 8481) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta8292_psi_8467_bounds.2]
  · change Chebyshev.theta (↑(8508 : ℕ) : ℝ) ≤ (8466100 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 8508
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 8501) (b := 8508) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta8292_psi_8501_bounds.2]
  · change Chebyshev.theta (↑(8517 : ℕ) : ℝ) ≤ (8475111 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 8517
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 8513) (b := 8517) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta8292_psi_8513_bounds.2]
  · change Chebyshev.theta (↑(8526 : ℕ) : ℝ) ≤ (8484122 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 8526
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 8521) (b := 8526) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta8292_psi_8521_bounds.2]
  · change Chebyshev.theta (↑(8544 : ℕ) : ℝ) ≤ (8520859 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 8544
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 8543) (b := 8544) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta8292_psi_8543_bounds.2]
  · change Chebyshev.theta (↑(8572 : ℕ) : ℝ) ≤ (8529870 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 8572
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 8563) (b := 8572) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta8292_psi_8563_bounds.2]
  · change Chebyshev.theta (↑(8590 : ℕ) : ℝ) ≤ (8547892 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 8590
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 8581) (b := 8590) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta8292_psi_8581_bounds.2]
  · change Chebyshev.theta (↑(8599 : ℕ) : ℝ) ≤ (8565913 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 8599
    linarith only [hd, theta8292_psi_8599_bounds.2]

/-- The envelope bound applies at every cell a endpoint. -/
theorem theta8292_a :
    ∀ r ∈ theta8292Cells,
      (r.ca : ℝ) / 1000 ≤
        Real.sqrt r.a *
          (Real.log r.a * (Real.log r.a - Real.log (Real.log r.a)) / (8 * Real.pi)) := by
  intro r hr
  simp only [theta8292Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 8292 *
          (Real.log 8292 * (Real.log 8292 - Real.log (Real.log 8292)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 8337 *
          (Real.log 8337 * (Real.log 8337 - Real.log (Real.log 8337)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 8383 *
          (Real.log 8383 * (Real.log 8383 - Real.log (Real.log 8383)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 8419 *
          (Real.log 8419 * (Real.log 8419 - Real.log (Real.log 8419)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 8446 *
          (Real.log 8446 * (Real.log 8446 - Real.log (Real.log 8446)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 8482 *
          (Real.log 8482 * (Real.log 8482 - Real.log (Real.log 8482)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 8509 *
          (Real.log 8509 * (Real.log 8509 - Real.log (Real.log 8509)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 8518 *
          (Real.log 8518 * (Real.log 8518 - Real.log (Real.log 8518)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 8527 *
          (Real.log 8527 * (Real.log 8527 - Real.log (Real.log 8527)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 8545 *
          (Real.log 8545 * (Real.log 8545 - Real.log (Real.log 8545)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 8573 *
          (Real.log 8573 * (Real.log 8573 - Real.log (Real.log 8573)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 8591 *
          (Real.log 8591 * (Real.log 8591 - Real.log (Real.log 8591)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)

/-- The envelope bound applies at every cell b endpoint. -/
theorem theta8292_b :
    ∀ r ∈ theta8292Cells,
      (r.cb : ℝ) / 1000 ≤
        Real.sqrt r.b *
          (Real.log r.b * (Real.log r.b - Real.log (Real.log r.b)) / (8 * Real.pi)) := by
  intro r hr
  simp only [theta8292Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 8337 *
          (Real.log 8337 * (Real.log 8337 - Real.log (Real.log 8337)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 8383 *
          (Real.log 8383 * (Real.log 8383 - Real.log (Real.log 8383)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 8419 *
          (Real.log 8419 * (Real.log 8419 - Real.log (Real.log 8419)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 8446 *
          (Real.log 8446 * (Real.log 8446 - Real.log (Real.log 8446)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 8482 *
          (Real.log 8482 * (Real.log 8482 - Real.log (Real.log 8482)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 8509 *
          (Real.log 8509 * (Real.log 8509 - Real.log (Real.log 8509)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 8518 *
          (Real.log 8518 * (Real.log 8518 - Real.log (Real.log 8518)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 8527 *
          (Real.log 8527 * (Real.log 8527 - Real.log (Real.log 8527)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 8545 *
          (Real.log 8545 * (Real.log 8545 - Real.log (Real.log 8545)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 8573 *
          (Real.log 8573 * (Real.log 8573 - Real.log (Real.log 8573)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 8591 *
          (Real.log 8591 * (Real.log 8591 - Real.log (Real.log 8591)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 8600 *
          (Real.log 8600 * (Real.log 8600 - Real.log (Real.log 8600)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)

/-- The cells form a checked chain covering `[8292, 8600)`. -/
theorem theta8292_check : leeNosalChainCheck 8292 8600 theta8292Cells = true := by decide +kernel

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
