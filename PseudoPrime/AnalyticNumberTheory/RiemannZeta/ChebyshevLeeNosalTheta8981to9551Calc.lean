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
def theta8981Cells : List LeeNosalCell :=
  [⟨8981, 9026, 8815423, 9019925, 211000, 211000⟩, ⟨9026, 9072, 8861171, 9074683, 211000, 211000⟩,
    ⟨9072, 9126, 8915929, 9101716, 211000, 211000⟩, ⟨9126, 9153, 8942962, 9138453, 211000, 211000⟩,
    ⟨9153, 9190, 8979699, 9184201, 211000, 211000⟩, ⟨9190, 9236, 9025446, 9229948, 211000, 211000⟩,
    ⟨9236, 9282, 9071194, 9275696, 211000, 211000⟩, ⟨9282, 9327, 9116942, 9320751, 211000, 211000⟩,
    ⟨9327, 9372, 9161996, 9366498, 211000, 211000⟩, ⟨9372, 9418, 9207744, 9417098, 211000, 211000⟩,
    ⟨9418, 9469, 9258344, 9499583, 211000, 211000⟩, ⟨9469, 9551, 9340828, 9582067, 211000, 211000⟩]

/-- The kernel-checked prefix bounds for 8971. -/
theorem theta8981_psi_8971_bounds :
    (8973483 : ℝ) / 1000 ≤ Chebyshev.psi 8971 ∧ Chebyshev.psi 8971 ≤ (8974177 : ℝ) / 1000 := by
  have hl : 2 ^ 12946 ≤ Nat.lcmUpto 8971 := by decide +kernel
  have hu : Nat.lcmUpto 8971 ≤ 2 ^ (12946 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 9013. -/
theorem theta8981_psi_9013_bounds :
    (9019231 : ℝ) / 1000 ≤ Chebyshev.psi 9013 ∧ Chebyshev.psi 9013 ≤ (9019925 : ℝ) / 1000 := by
  have hl : 2 ^ 13012 ≤ Nat.lcmUpto 9013 := by decide +kernel
  have hu : Nat.lcmUpto 9013 ≤ 2 ^ (13012 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 9067. -/
theorem theta8981_psi_9067_bounds :
    (9073989 : ℝ) / 1000 ≤ Chebyshev.psi 9067 ∧ Chebyshev.psi 9067 ≤ (9074683 : ℝ) / 1000 := by
  have hl : 2 ^ 13091 ≤ Nat.lcmUpto 9067 := by decide +kernel
  have hu : Nat.lcmUpto 9067 ≤ 2 ^ (13091 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 9109. -/
theorem theta8981_psi_9109_bounds :
    (9101022 : ℝ) / 1000 ≤ Chebyshev.psi 9109 ∧ Chebyshev.psi 9109 ≤ (9101716 : ℝ) / 1000 := by
  have hl : 2 ^ 13130 ≤ Nat.lcmUpto 9109 := by decide +kernel
  have hu : Nat.lcmUpto 9109 ≤ 2 ^ (13130 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 9151. -/
theorem theta8981_psi_9151_bounds :
    (9137759 : ℝ) / 1000 ≤ Chebyshev.psi 9151 ∧ Chebyshev.psi 9151 ≤ (9138453 : ℝ) / 1000 := by
  have hl : 2 ^ 13183 ≤ Nat.lcmUpto 9151 := by decide +kernel
  have hu : Nat.lcmUpto 9151 ≤ 2 ^ (13183 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 9187. -/
theorem theta8981_psi_9187_bounds :
    (9183506 : ℝ) / 1000 ≤ Chebyshev.psi 9187 ∧ Chebyshev.psi 9187 ≤ (9184201 : ℝ) / 1000 := by
  have hl : 2 ^ 13249 ≤ Nat.lcmUpto 9187 := by decide +kernel
  have hu : Nat.lcmUpto 9187 ≤ 2 ^ (13249 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 9227. -/
theorem theta8981_psi_9227_bounds :
    (9229254 : ℝ) / 1000 ≤ Chebyshev.psi 9227 ∧ Chebyshev.psi 9227 ≤ (9229948 : ℝ) / 1000 := by
  have hl : 2 ^ 13315 ≤ Nat.lcmUpto 9227 := by decide +kernel
  have hu : Nat.lcmUpto 9227 ≤ 2 ^ (13315 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 9281. -/
theorem theta8981_psi_9281_bounds :
    (9275002 : ℝ) / 1000 ≤ Chebyshev.psi 9281 ∧ Chebyshev.psi 9281 ≤ (9275696 : ℝ) / 1000 := by
  have hl : 2 ^ 13381 ≤ Nat.lcmUpto 9281 := by decide +kernel
  have hu : Nat.lcmUpto 9281 ≤ 2 ^ (13381 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 9323. -/
theorem theta8981_psi_9323_bounds :
    (9320056 : ℝ) / 1000 ≤ Chebyshev.psi 9323 ∧ Chebyshev.psi 9323 ≤ (9320751 : ℝ) / 1000 := by
  have hl : 2 ^ 13446 ≤ Nat.lcmUpto 9323 := by decide +kernel
  have hu : Nat.lcmUpto 9323 ≤ 2 ^ (13446 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 9371. -/
theorem theta8981_psi_9371_bounds :
    (9365804 : ℝ) / 1000 ≤ Chebyshev.psi 9371 ∧ Chebyshev.psi 9371 ≤ (9366498 : ℝ) / 1000 := by
  have hl : 2 ^ 13512 ≤ Nat.lcmUpto 9371 := by decide +kernel
  have hu : Nat.lcmUpto 9371 ≤ 2 ^ (13512 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 9413. -/
theorem theta8981_psi_9413_bounds :
    (9416404 : ℝ) / 1000 ≤ Chebyshev.psi 9413 ∧ Chebyshev.psi 9413 ≤ (9417098 : ℝ) / 1000 := by
  have hl : 2 ^ 13585 ≤ Nat.lcmUpto 9413 := by decide +kernel
  have hu : Nat.lcmUpto 9413 ≤ 2 ^ (13585 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 9467. -/
theorem theta8981_psi_9467_bounds :
    (9498888 : ℝ) / 1000 ≤ Chebyshev.psi 9467 ∧ Chebyshev.psi 9467 ≤ (9499583 : ℝ) / 1000 := by
  have hl : 2 ^ 13704 ≤ Nat.lcmUpto 9467 := by decide +kernel
  have hu : Nat.lcmUpto 9467 ≤ 2 ^ (13704 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 9547. -/
theorem theta8981_psi_9547_bounds :
    (9581373 : ℝ) / 1000 ≤ Chebyshev.psi 9547 ∧ Chebyshev.psi 9547 ≤ (9582067 : ℝ) / 1000 := by
  have hl : 2 ^ 13823 ≤ Nat.lcmUpto 9547 := by decide +kernel
  have hu : Nat.lcmUpto 9547 ≤ 2 ^ (13823 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- Every batch cell has a checked theta lower bound. -/
theorem theta8981_lower : ∀ r ∈ theta8981Cells, (r.lo : ℝ) / 1000 ≤ Chebyshev.theta r.a := by
  intro r hr
  simp only [theta8981Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change (8815423 : ℝ) / 1000 ≤ Chebyshev.theta (↑(8981 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 8981) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 8971) (b := 8981) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta8981_psi_8971_bounds.1]
  · change (8861171 : ℝ) / 1000 ≤ Chebyshev.theta (↑(9026 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 9026) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 9013) (b := 9026) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta8981_psi_9013_bounds.1]
  · change (8915929 : ℝ) / 1000 ≤ Chebyshev.theta (↑(9072 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 9072) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 9067) (b := 9072) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta8981_psi_9067_bounds.1]
  · change (8942962 : ℝ) / 1000 ≤ Chebyshev.theta (↑(9126 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 9126) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 9109) (b := 9126) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta8981_psi_9109_bounds.1]
  · change (8979699 : ℝ) / 1000 ≤ Chebyshev.theta (↑(9153 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 9153) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 9151) (b := 9153) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta8981_psi_9151_bounds.1]
  · change (9025446 : ℝ) / 1000 ≤ Chebyshev.theta (↑(9190 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 9190) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 9187) (b := 9190) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta8981_psi_9187_bounds.1]
  · change (9071194 : ℝ) / 1000 ≤ Chebyshev.theta (↑(9236 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 9236) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 9227) (b := 9236) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta8981_psi_9227_bounds.1]
  · change (9116942 : ℝ) / 1000 ≤ Chebyshev.theta (↑(9282 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 9282) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 9281) (b := 9282) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta8981_psi_9281_bounds.1]
  · change (9161996 : ℝ) / 1000 ≤ Chebyshev.theta (↑(9327 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 9327) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 9323) (b := 9327) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta8981_psi_9323_bounds.1]
  · change (9207744 : ℝ) / 1000 ≤ Chebyshev.theta (↑(9372 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 9372) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 9371) (b := 9372) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta8981_psi_9371_bounds.1]
  · change (9258344 : ℝ) / 1000 ≤ Chebyshev.theta (↑(9418 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 9418) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 9413) (b := 9418) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta8981_psi_9413_bounds.1]
  · change (9340828 : ℝ) / 1000 ≤ Chebyshev.theta (↑(9469 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 9469) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 9467) (b := 9469) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta8981_psi_9467_bounds.1]

/-- Every batch cell has a checked theta upper bound. -/
theorem theta8981_upper :
    ∀ r ∈ theta8981Cells, Chebyshev.theta (r.b - 1 : ℕ) ≤ (r.hi : ℝ) / 1000 := by
  intro r hr
  simp only [theta8981Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change Chebyshev.theta (↑(9025 : ℕ) : ℝ) ≤ (9019925 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 9025
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 9013) (b := 9025) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta8981_psi_9013_bounds.2]
  · change Chebyshev.theta (↑(9071 : ℕ) : ℝ) ≤ (9074683 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 9071
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 9067) (b := 9071) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta8981_psi_9067_bounds.2]
  · change Chebyshev.theta (↑(9125 : ℕ) : ℝ) ≤ (9101716 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 9125
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 9109) (b := 9125) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta8981_psi_9109_bounds.2]
  · change Chebyshev.theta (↑(9152 : ℕ) : ℝ) ≤ (9138453 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 9152
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 9151) (b := 9152) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta8981_psi_9151_bounds.2]
  · change Chebyshev.theta (↑(9189 : ℕ) : ℝ) ≤ (9184201 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 9189
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 9187) (b := 9189) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta8981_psi_9187_bounds.2]
  · change Chebyshev.theta (↑(9235 : ℕ) : ℝ) ≤ (9229948 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 9235
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 9227) (b := 9235) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta8981_psi_9227_bounds.2]
  · change Chebyshev.theta (↑(9281 : ℕ) : ℝ) ≤ (9275696 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 9281
    linarith only [hd, theta8981_psi_9281_bounds.2]
  · change Chebyshev.theta (↑(9326 : ℕ) : ℝ) ≤ (9320751 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 9326
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 9323) (b := 9326) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta8981_psi_9323_bounds.2]
  · change Chebyshev.theta (↑(9371 : ℕ) : ℝ) ≤ (9366498 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 9371
    linarith only [hd, theta8981_psi_9371_bounds.2]
  · change Chebyshev.theta (↑(9417 : ℕ) : ℝ) ≤ (9417098 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 9417
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 9413) (b := 9417) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta8981_psi_9413_bounds.2]
  · change Chebyshev.theta (↑(9468 : ℕ) : ℝ) ≤ (9499583 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 9468
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 9467) (b := 9468) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta8981_psi_9467_bounds.2]
  · change Chebyshev.theta (↑(9550 : ℕ) : ℝ) ≤ (9582067 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 9550
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 9547) (b := 9550) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta8981_psi_9547_bounds.2]

/-- The envelope bound applies at every cell a endpoint. -/
theorem theta8981_a :
    ∀ r ∈ theta8981Cells,
      (r.ca : ℝ) / 1000 ≤
        Real.sqrt r.a *
          (Real.log r.a * (Real.log r.a - Real.log (Real.log r.a)) / (8 * Real.pi)) := by
  intro r hr
  simp only [theta8981Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 8981 *
          (Real.log 8981 * (Real.log 8981 - Real.log (Real.log 8981)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 9026 *
          (Real.log 9026 * (Real.log 9026 - Real.log (Real.log 9026)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 9072 *
          (Real.log 9072 * (Real.log 9072 - Real.log (Real.log 9072)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 9126 *
          (Real.log 9126 * (Real.log 9126 - Real.log (Real.log 9126)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 9153 *
          (Real.log 9153 * (Real.log 9153 - Real.log (Real.log 9153)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 9190 *
          (Real.log 9190 * (Real.log 9190 - Real.log (Real.log 9190)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 9236 *
          (Real.log 9236 * (Real.log 9236 - Real.log (Real.log 9236)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 9282 *
          (Real.log 9282 * (Real.log 9282 - Real.log (Real.log 9282)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 9327 *
          (Real.log 9327 * (Real.log 9327 - Real.log (Real.log 9327)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 9372 *
          (Real.log 9372 * (Real.log 9372 - Real.log (Real.log 9372)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 9418 *
          (Real.log 9418 * (Real.log 9418 - Real.log (Real.log 9418)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 9469 *
          (Real.log 9469 * (Real.log 9469 - Real.log (Real.log 9469)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)

/-- The envelope bound applies at every cell b endpoint. -/
theorem theta8981_b :
    ∀ r ∈ theta8981Cells,
      (r.cb : ℝ) / 1000 ≤
        Real.sqrt r.b *
          (Real.log r.b * (Real.log r.b - Real.log (Real.log r.b)) / (8 * Real.pi)) := by
  intro r hr
  simp only [theta8981Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 9026 *
          (Real.log 9026 * (Real.log 9026 - Real.log (Real.log 9026)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 9072 *
          (Real.log 9072 * (Real.log 9072 - Real.log (Real.log 9072)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 9126 *
          (Real.log 9126 * (Real.log 9126 - Real.log (Real.log 9126)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 9153 *
          (Real.log 9153 * (Real.log 9153 - Real.log (Real.log 9153)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 9190 *
          (Real.log 9190 * (Real.log 9190 - Real.log (Real.log 9190)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 9236 *
          (Real.log 9236 * (Real.log 9236 - Real.log (Real.log 9236)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 9282 *
          (Real.log 9282 * (Real.log 9282 - Real.log (Real.log 9282)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 9327 *
          (Real.log 9327 * (Real.log 9327 - Real.log (Real.log 9327)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 9372 *
          (Real.log 9372 * (Real.log 9372 - Real.log (Real.log 9372)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 9418 *
          (Real.log 9418 * (Real.log 9418 - Real.log (Real.log 9418)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 9469 *
          (Real.log 9469 * (Real.log 9469 - Real.log (Real.log 9469)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 9551 *
          (Real.log 9551 * (Real.log 9551 - Real.log (Real.log 9551)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)

/-- The cells form a checked chain covering `[8981, 9551)`. -/
theorem theta8981_check : leeNosalChainCheck 8981 9551 theta8981Cells = true := by decide +kernel

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
