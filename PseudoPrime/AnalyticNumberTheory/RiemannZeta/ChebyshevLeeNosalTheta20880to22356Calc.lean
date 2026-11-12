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
def theta20880Cells : List LeeNosalCell :=
  [⟨20880, 20969, 20604465, 20929580, 365000, 365000⟩,
    ⟨20969, 21068, 20703585, 21049494, 365000, 365000⟩,
    ⟨21068, 21188, 20823500, 21168715, 365000, 365000⟩,
    ⟨21188, 21307, 20942721, 21258131, 365000, 365000⟩,
    ⟨21307, 21397, 21032137, 21357945, 365000, 365000⟩,
    ⟨21397, 21507, 21142348, 21477859, 365000, 365000⟩,
    ⟨21507, 21616, 21251865, 21627579, 365000, 365000⟩,
    ⟨21616, 21766, 21401585, 21757197, 365000, 365000⟩,
    ⟨21766, 21896, 21531203, 21906917, 365000, 365000⟩,
    ⟨21896, 22045, 21680923, 22046933, 365000, 365000⟩,
    ⟨22045, 22185, 21820939, 22217447, 365000, 365000⟩,
    ⟨22185, 22356, 21991453, 22372712, 365000, 365000⟩]

/-- The kernel-checked prefix bounds for 20879. -/
theorem theta20880_psi_20879_bounds :
    (20829765 : ℝ) / 1000 ≤ Chebyshev.psi 20879 ∧ Chebyshev.psi 20879 ≤ (20830460 : ℝ) / 1000 := by
  have hl : 2 ^ 30051 ≤ Nat.lcmUpto 20879 := by decide +kernel
  have hu : Nat.lcmUpto 20879 ≤ 2 ^ (30051 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 20963. -/
theorem theta20880_psi_20963_bounds :
    (20928885 : ℝ) / 1000 ≤ Chebyshev.psi 20963 ∧ Chebyshev.psi 20963 ≤ (20929580 : ℝ) / 1000 := by
  have hl : 2 ^ 30194 ≤ Nat.lcmUpto 20963 := by decide +kernel
  have hu : Nat.lcmUpto 20963 ≤ 2 ^ (30194 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 21067. -/
theorem theta20880_psi_21067_bounds :
    (21048800 : ℝ) / 1000 ≤ Chebyshev.psi 21067 ∧ Chebyshev.psi 21067 ≤ (21049494 : ℝ) / 1000 := by
  have hl : 2 ^ 30367 ≤ Nat.lcmUpto 21067 := by decide +kernel
  have hu : Nat.lcmUpto 21067 ≤ 2 ^ (30367 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 21187. -/
theorem theta20880_psi_21187_bounds :
    (21168021 : ℝ) / 1000 ≤ Chebyshev.psi 21187 ∧ Chebyshev.psi 21187 ≤ (21168715 : ℝ) / 1000 := by
  have hl : 2 ^ 30539 ≤ Nat.lcmUpto 21187 := by decide +kernel
  have hu : Nat.lcmUpto 21187 ≤ 2 ^ (30539 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 21283. -/
theorem theta20880_psi_21283_bounds :
    (21257437 : ℝ) / 1000 ≤ Chebyshev.psi 21283 ∧ Chebyshev.psi 21283 ≤ (21258131 : ℝ) / 1000 := by
  have hl : 2 ^ 30668 ≤ Nat.lcmUpto 21283 := by decide +kernel
  have hu : Nat.lcmUpto 21283 ≤ 2 ^ (30668 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 21391. -/
theorem theta20880_psi_21391_bounds :
    (21357250 : ℝ) / 1000 ≤ Chebyshev.psi 21391 ∧ Chebyshev.psi 21391 ≤ (21357945 : ℝ) / 1000 := by
  have hl : 2 ^ 30812 ≤ Nat.lcmUpto 21391 := by decide +kernel
  have hu : Nat.lcmUpto 21391 ≤ 2 ^ (30812 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 21397. -/
theorem theta20880_psi_21397_bounds :
    (21367648 : ℝ) / 1000 ≤ Chebyshev.psi 21397 ∧ Chebyshev.psi 21397 ≤ (21368342 : ℝ) / 1000 := by
  have hl : 2 ^ 30827 ≤ Nat.lcmUpto 21397 := by decide +kernel
  have hu : Nat.lcmUpto 21397 ≤ 2 ^ (30827 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 21503. -/
theorem theta20880_psi_21503_bounds :
    (21477165 : ℝ) / 1000 ≤ Chebyshev.psi 21503 ∧ Chebyshev.psi 21503 ≤ (21477859 : ℝ) / 1000 := by
  have hl : 2 ^ 30985 ≤ Nat.lcmUpto 21503 := by decide +kernel
  have hu : Nat.lcmUpto 21503 ≤ 2 ^ (30985 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 21613. -/
theorem theta20880_psi_21613_bounds :
    (21626885 : ℝ) / 1000 ≤ Chebyshev.psi 21613 ∧ Chebyshev.psi 21613 ≤ (21627579 : ℝ) / 1000 := by
  have hl : 2 ^ 31201 ≤ Nat.lcmUpto 21613 := by decide +kernel
  have hu : Nat.lcmUpto 21613 ≤ 2 ^ (31201 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 21757. -/
theorem theta20880_psi_21757_bounds :
    (21756503 : ℝ) / 1000 ≤ Chebyshev.psi 21757 ∧ Chebyshev.psi 21757 ≤ (21757197 : ℝ) / 1000 := by
  have hl : 2 ^ 31388 ≤ Nat.lcmUpto 21757 := by decide +kernel
  have hu : Nat.lcmUpto 21757 ≤ 2 ^ (31388 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 21893. -/
theorem theta20880_psi_21893_bounds :
    (21906223 : ℝ) / 1000 ≤ Chebyshev.psi 21893 ∧ Chebyshev.psi 21893 ≤ (21906917 : ℝ) / 1000 := by
  have hl : 2 ^ 31604 ≤ Nat.lcmUpto 21893 := by decide +kernel
  have hu : Nat.lcmUpto 21893 ≤ 2 ^ (31604 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 22039. -/
theorem theta20880_psi_22039_bounds :
    (22046239 : ℝ) / 1000 ≤ Chebyshev.psi 22039 ∧ Chebyshev.psi 22039 ≤ (22046933 : ℝ) / 1000 := by
  have hl : 2 ^ 31806 ≤ Nat.lcmUpto 22039 := by decide +kernel
  have hu : Nat.lcmUpto 22039 ≤ 2 ^ (31806 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 22171. -/
theorem theta20880_psi_22171_bounds :
    (22216753 : ℝ) / 1000 ≤ Chebyshev.psi 22171 ∧ Chebyshev.psi 22171 ≤ (22217447 : ℝ) / 1000 := by
  have hl : 2 ^ 32052 ≤ Nat.lcmUpto 22171 := by decide +kernel
  have hu : Nat.lcmUpto 22171 ≤ 2 ^ (32052 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 22349. -/
theorem theta20880_psi_22349_bounds :
    (22372018 : ℝ) / 1000 ≤ Chebyshev.psi 22349 ∧ Chebyshev.psi 22349 ≤ (22372712 : ℝ) / 1000 := by
  have hl : 2 ^ 32276 ≤ Nat.lcmUpto 22349 := by decide +kernel
  have hu : Nat.lcmUpto 22349 ≤ 2 ^ (32276 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- Every batch cell has a checked theta lower bound. -/
theorem theta20880_lower : ∀ r ∈ theta20880Cells, (r.lo : ℝ) / 1000 ≤ Chebyshev.theta r.a := by
  intro r hr
  simp only [theta20880Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change (20604465 : ℝ) / 1000 ≤ Chebyshev.theta (↑(20880 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 20880) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 20879) (b := 20880) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta20880_psi_20879_bounds.1]
  · change (20703585 : ℝ) / 1000 ≤ Chebyshev.theta (↑(20969 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 20969) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 20963) (b := 20969) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta20880_psi_20963_bounds.1]
  · change (20823500 : ℝ) / 1000 ≤ Chebyshev.theta (↑(21068 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 21068) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 21067) (b := 21068) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta20880_psi_21067_bounds.1]
  · change (20942721 : ℝ) / 1000 ≤ Chebyshev.theta (↑(21188 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 21188) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 21187) (b := 21188) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta20880_psi_21187_bounds.1]
  · change (21032137 : ℝ) / 1000 ≤ Chebyshev.theta (↑(21307 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 21307) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 21283) (b := 21307) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta20880_psi_21283_bounds.1]
  · change (21142348 : ℝ) / 1000 ≤ Chebyshev.theta (↑(21397 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 21397) (by norm_num only) (by norm_num only)
    linarith only [hd, theta20880_psi_21397_bounds.1]
  · change (21251865 : ℝ) / 1000 ≤ Chebyshev.theta (↑(21507 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 21507) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 21503) (b := 21507) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta20880_psi_21503_bounds.1]
  · change (21401585 : ℝ) / 1000 ≤ Chebyshev.theta (↑(21616 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 21616) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 21613) (b := 21616) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta20880_psi_21613_bounds.1]
  · change (21531203 : ℝ) / 1000 ≤ Chebyshev.theta (↑(21766 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 21766) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 21757) (b := 21766) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta20880_psi_21757_bounds.1]
  · change (21680923 : ℝ) / 1000 ≤ Chebyshev.theta (↑(21896 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 21896) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 21893) (b := 21896) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta20880_psi_21893_bounds.1]
  · change (21820939 : ℝ) / 1000 ≤ Chebyshev.theta (↑(22045 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 22045) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 22039) (b := 22045) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta20880_psi_22039_bounds.1]
  · change (21991453 : ℝ) / 1000 ≤ Chebyshev.theta (↑(22185 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 22185) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 22171) (b := 22185) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta20880_psi_22171_bounds.1]

/-- Every batch cell has a checked theta upper bound. -/
theorem theta20880_upper :
    ∀ r ∈ theta20880Cells, Chebyshev.theta (r.b - 1 : ℕ) ≤ (r.hi : ℝ) / 1000 := by
  intro r hr
  simp only [theta20880Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change Chebyshev.theta (↑(20968 : ℕ) : ℝ) ≤ (20929580 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 20968
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 20963) (b := 20968) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta20880_psi_20963_bounds.2]
  · change Chebyshev.theta (↑(21067 : ℕ) : ℝ) ≤ (21049494 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 21067
    linarith only [hd, theta20880_psi_21067_bounds.2]
  · change Chebyshev.theta (↑(21187 : ℕ) : ℝ) ≤ (21168715 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 21187
    linarith only [hd, theta20880_psi_21187_bounds.2]
  · change Chebyshev.theta (↑(21306 : ℕ) : ℝ) ≤ (21258131 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 21306
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 21283) (b := 21306) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta20880_psi_21283_bounds.2]
  · change Chebyshev.theta (↑(21396 : ℕ) : ℝ) ≤ (21357945 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 21396
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 21391) (b := 21396) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta20880_psi_21391_bounds.2]
  · change Chebyshev.theta (↑(21506 : ℕ) : ℝ) ≤ (21477859 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 21506
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 21503) (b := 21506) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta20880_psi_21503_bounds.2]
  · change Chebyshev.theta (↑(21615 : ℕ) : ℝ) ≤ (21627579 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 21615
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 21613) (b := 21615) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta20880_psi_21613_bounds.2]
  · change Chebyshev.theta (↑(21765 : ℕ) : ℝ) ≤ (21757197 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 21765
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 21757) (b := 21765) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta20880_psi_21757_bounds.2]
  · change Chebyshev.theta (↑(21895 : ℕ) : ℝ) ≤ (21906917 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 21895
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 21893) (b := 21895) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta20880_psi_21893_bounds.2]
  · change Chebyshev.theta (↑(22044 : ℕ) : ℝ) ≤ (22046933 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 22044
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 22039) (b := 22044) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta20880_psi_22039_bounds.2]
  · change Chebyshev.theta (↑(22184 : ℕ) : ℝ) ≤ (22217447 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 22184
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 22171) (b := 22184) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta20880_psi_22171_bounds.2]
  · change Chebyshev.theta (↑(22355 : ℕ) : ℝ) ≤ (22372712 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 22355
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 22349) (b := 22355) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta20880_psi_22349_bounds.2]

/-- The envelope bound applies at every cell a endpoint. -/
theorem theta20880_a :
    ∀ r ∈ theta20880Cells,
      (r.ca : ℝ) / 1000 ≤
        Real.sqrt r.a *
          (Real.log r.a * (Real.log r.a - Real.log (Real.log r.a)) / (8 * Real.pi)) := by
  intro r hr
  simp only [theta20880Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 20880 *
          (Real.log 20880 * (Real.log 20880 - Real.log (Real.log 20880)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 20969 *
          (Real.log 20969 * (Real.log 20969 - Real.log (Real.log 20969)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 21068 *
          (Real.log 21068 * (Real.log 21068 - Real.log (Real.log 21068)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 21188 *
          (Real.log 21188 * (Real.log 21188 - Real.log (Real.log 21188)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 21307 *
          (Real.log 21307 * (Real.log 21307 - Real.log (Real.log 21307)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 21397 *
          (Real.log 21397 * (Real.log 21397 - Real.log (Real.log 21397)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 21507 *
          (Real.log 21507 * (Real.log 21507 - Real.log (Real.log 21507)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 21616 *
          (Real.log 21616 * (Real.log 21616 - Real.log (Real.log 21616)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 21766 *
          (Real.log 21766 * (Real.log 21766 - Real.log (Real.log 21766)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 21896 *
          (Real.log 21896 * (Real.log 21896 - Real.log (Real.log 21896)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 22045 *
          (Real.log 22045 * (Real.log 22045 - Real.log (Real.log 22045)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 22185 *
          (Real.log 22185 * (Real.log 22185 - Real.log (Real.log 22185)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)

/-- The envelope bound applies at every cell b endpoint. -/
theorem theta20880_b :
    ∀ r ∈ theta20880Cells,
      (r.cb : ℝ) / 1000 ≤
        Real.sqrt r.b *
          (Real.log r.b * (Real.log r.b - Real.log (Real.log r.b)) / (8 * Real.pi)) := by
  intro r hr
  simp only [theta20880Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 20969 *
          (Real.log 20969 * (Real.log 20969 - Real.log (Real.log 20969)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 21068 *
          (Real.log 21068 * (Real.log 21068 - Real.log (Real.log 21068)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 21188 *
          (Real.log 21188 * (Real.log 21188 - Real.log (Real.log 21188)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 21307 *
          (Real.log 21307 * (Real.log 21307 - Real.log (Real.log 21307)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 21397 *
          (Real.log 21397 * (Real.log 21397 - Real.log (Real.log 21397)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 21507 *
          (Real.log 21507 * (Real.log 21507 - Real.log (Real.log 21507)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 21616 *
          (Real.log 21616 * (Real.log 21616 - Real.log (Real.log 21616)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 21766 *
          (Real.log 21766 * (Real.log 21766 - Real.log (Real.log 21766)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 21896 *
          (Real.log 21896 * (Real.log 21896 - Real.log (Real.log 21896)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 22045 *
          (Real.log 22045 * (Real.log 22045 - Real.log (Real.log 22045)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 22185 *
          (Real.log 22185 * (Real.log 22185 - Real.log (Real.log 22185)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 22356 *
          (Real.log 22356 * (Real.log 22356 - Real.log (Real.log 22356)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)

/-- The cells form a checked chain covering `[20880, 22356)`. -/
theorem theta20880_check : leeNosalChainCheck 20880 22356 theta20880Cells = true := by
  decide +kernel

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
