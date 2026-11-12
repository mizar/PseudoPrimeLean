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
def theta16384Cells : List LeeNosalCell :=
  [⟨16384, 16547, 16182880, 16544731, 365000, 365000⟩,
    ⟨16547, 16693, 16328440, 16699996, 365000, 365000⟩,
    ⟨16693, 16848, 16483705, 16838625, 365000, 365000⟩,
    ⟨16848, 16977, 16612631, 16955074, 365000, 365000⟩,
    ⟨16977, 17094, 16729080, 17091624, 365000, 365000⟩,
    ⟨17094, 17230, 16865630, 17223322, 365000, 365000⟩,
    ⟨17230, 17362, 16997327, 17350168, 365000, 365000⟩,
    ⟨17362, 17489, 17124173, 17496422, 365000, 365000⟩,
    ⟨17489, 17645, 17280132, 17653073, 365000, 365000⟩,
    ⟨17645, 17792, 17427079, 17800020, 365000, 365000⟩,
    ⟨17792, 17939, 17574026, 17936570, 365000, 365000⟩,
    ⟨17939, 18085, 17720280, 18093915, 365000, 365000⟩]

/-- The kernel-checked prefix bounds for 16384. -/
theorem theta16384_psi_16384_bounds :
    (16408180 : ℝ) / 1000 ≤ Chebyshev.psi 16384 ∧ Chebyshev.psi 16384 ≤ (16408874 : ℝ) / 1000 := by
  have hl : 2 ^ 23672 ≤ Nat.lcmUpto 16384 := by decide +kernel
  have hu : Nat.lcmUpto 16384 ≤ 2 ^ (23672 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 16529. -/
theorem theta16384_psi_16529_bounds :
    (16544036 : ℝ) / 1000 ≤ Chebyshev.psi 16529 ∧ Chebyshev.psi 16529 ≤ (16544731 : ℝ) / 1000 := by
  have hl : 2 ^ 23868 ≤ Nat.lcmUpto 16529 := by decide +kernel
  have hu : Nat.lcmUpto 16529 ≤ 2 ^ (23868 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 16547. -/
theorem theta16384_psi_16547_bounds :
    (16553740 : ℝ) / 1000 ≤ Chebyshev.psi 16547 ∧ Chebyshev.psi 16547 ≤ (16554435 : ℝ) / 1000 := by
  have hl : 2 ^ 23882 ≤ Nat.lcmUpto 16547 := by decide +kernel
  have hu : Nat.lcmUpto 16547 ≤ 2 ^ (23882 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 16691. -/
theorem theta16384_psi_16691_bounds :
    (16699301 : ℝ) / 1000 ≤ Chebyshev.psi 16691 ∧ Chebyshev.psi 16691 ≤ (16699996 : ℝ) / 1000 := by
  have hl : 2 ^ 24092 ≤ Nat.lcmUpto 16691 := by decide +kernel
  have hu : Nat.lcmUpto 16691 ≤ 2 ^ (24092 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 16693. -/
theorem theta16384_psi_16693_bounds :
    (16709005 : ℝ) / 1000 ≤ Chebyshev.psi 16693 ∧ Chebyshev.psi 16693 ≤ (16709700 : ℝ) / 1000 := by
  have hl : 2 ^ 24106 ≤ Nat.lcmUpto 16693 := by decide +kernel
  have hu : Nat.lcmUpto 16693 ≤ 2 ^ (24106 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 16843. -/
theorem theta16384_psi_16843_bounds :
    (16837931 : ℝ) / 1000 ≤ Chebyshev.psi 16843 ∧ Chebyshev.psi 16843 ≤ (16838625 : ℝ) / 1000 := by
  have hl : 2 ^ 24292 ≤ Nat.lcmUpto 16843 := by decide +kernel
  have hu : Nat.lcmUpto 16843 ≤ 2 ^ (24292 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 16963. -/
theorem theta16384_psi_16963_bounds :
    (16954380 : ℝ) / 1000 ≤ Chebyshev.psi 16963 ∧ Chebyshev.psi 16963 ≤ (16955074 : ℝ) / 1000 := by
  have hl : 2 ^ 24460 ≤ Nat.lcmUpto 16963 := by decide +kernel
  have hu : Nat.lcmUpto 16963 ≤ 2 ^ (24460 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 17093. -/
theorem theta16384_psi_17093_bounds :
    (17090930 : ℝ) / 1000 ≤ Chebyshev.psi 17093 ∧ Chebyshev.psi 17093 ≤ (17091624 : ℝ) / 1000 := by
  have hl : 2 ^ 24657 ≤ Nat.lcmUpto 17093 := by decide +kernel
  have hu : Nat.lcmUpto 17093 ≤ 2 ^ (24657 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 17209. -/
theorem theta16384_psi_17209_bounds :
    (17222627 : ℝ) / 1000 ≤ Chebyshev.psi 17209 ∧ Chebyshev.psi 17209 ≤ (17223322 : ℝ) / 1000 := by
  have hl : 2 ^ 24847 ≤ Nat.lcmUpto 17209 := by decide +kernel
  have hu : Nat.lcmUpto 17209 ≤ 2 ^ (24847 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 17359. -/
theorem theta16384_psi_17359_bounds :
    (17349473 : ℝ) / 1000 ≤ Chebyshev.psi 17359 ∧ Chebyshev.psi 17359 ≤ (17350168 : ℝ) / 1000 := by
  have hl : 2 ^ 25030 ≤ Nat.lcmUpto 17359 := by decide +kernel
  have hu : Nat.lcmUpto 17359 ≤ 2 ^ (25030 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 17483. -/
theorem theta16384_psi_17483_bounds :
    (17495727 : ℝ) / 1000 ≤ Chebyshev.psi 17483 ∧ Chebyshev.psi 17483 ≤ (17496422 : ℝ) / 1000 := by
  have hl : 2 ^ 25241 ≤ Nat.lcmUpto 17483 := by decide +kernel
  have hu : Nat.lcmUpto 17483 ≤ 2 ^ (25241 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 17489. -/
theorem theta16384_psi_17489_bounds :
    (17505432 : ℝ) / 1000 ≤ Chebyshev.psi 17489 ∧ Chebyshev.psi 17489 ≤ (17506126 : ℝ) / 1000 := by
  have hl : 2 ^ 25255 ≤ Nat.lcmUpto 17489 := by decide +kernel
  have hu : Nat.lcmUpto 17489 ≤ 2 ^ (25255 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 17627. -/
theorem theta16384_psi_17627_bounds :
    (17652379 : ℝ) / 1000 ≤ Chebyshev.psi 17627 ∧ Chebyshev.psi 17627 ≤ (17653073 : ℝ) / 1000 := by
  have hl : 2 ^ 25467 ≤ Nat.lcmUpto 17627 := by decide +kernel
  have hu : Nat.lcmUpto 17627 ≤ 2 ^ (25467 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 17791. -/
theorem theta16384_psi_17791_bounds :
    (17799326 : ℝ) / 1000 ≤ Chebyshev.psi 17791 ∧ Chebyshev.psi 17791 ≤ (17800020 : ℝ) / 1000 := by
  have hl : 2 ^ 25679 ≤ Nat.lcmUpto 17791 := by decide +kernel
  have hu : Nat.lcmUpto 17791 ≤ 2 ^ (25679 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 17929. -/
theorem theta16384_psi_17929_bounds :
    (17935876 : ℝ) / 1000 ≤ Chebyshev.psi 17929 ∧ Chebyshev.psi 17929 ≤ (17936570 : ℝ) / 1000 := by
  have hl : 2 ^ 25876 ≤ Nat.lcmUpto 17929 := by decide +kernel
  have hu : Nat.lcmUpto 17929 ≤ 2 ^ (25876 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 17939. -/
theorem theta16384_psi_17939_bounds :
    (17945580 : ℝ) / 1000 ≤ Chebyshev.psi 17939 ∧ Chebyshev.psi 17939 ≤ (17946274 : ℝ) / 1000 := by
  have hl : 2 ^ 25890 ≤ Nat.lcmUpto 17939 := by decide +kernel
  have hu : Nat.lcmUpto 17939 ≤ 2 ^ (25890 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 18077. -/
theorem theta16384_psi_18077_bounds :
    (18093220 : ℝ) / 1000 ≤ Chebyshev.psi 18077 ∧ Chebyshev.psi 18077 ≤ (18093915 : ℝ) / 1000 := by
  have hl : 2 ^ 26103 ≤ Nat.lcmUpto 18077 := by decide +kernel
  have hu : Nat.lcmUpto 18077 ≤ 2 ^ (26103 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- Every batch cell has a checked theta lower bound. -/
theorem theta16384_lower : ∀ r ∈ theta16384Cells, (r.lo : ℝ) / 1000 ≤ Chebyshev.theta r.a := by
  intro r hr
  simp only [theta16384Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change (16182880 : ℝ) / 1000 ≤ Chebyshev.theta (↑(16384 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 16384) (by norm_num only) (by norm_num only)
    linarith only [hd, theta16384_psi_16384_bounds.1]
  · change (16328440 : ℝ) / 1000 ≤ Chebyshev.theta (↑(16547 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 16547) (by norm_num only) (by norm_num only)
    linarith only [hd, theta16384_psi_16547_bounds.1]
  · change (16483705 : ℝ) / 1000 ≤ Chebyshev.theta (↑(16693 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 16693) (by norm_num only) (by norm_num only)
    linarith only [hd, theta16384_psi_16693_bounds.1]
  · change (16612631 : ℝ) / 1000 ≤ Chebyshev.theta (↑(16848 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 16848) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 16843) (b := 16848) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta16384_psi_16843_bounds.1]
  · change (16729080 : ℝ) / 1000 ≤ Chebyshev.theta (↑(16977 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 16977) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 16963) (b := 16977) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta16384_psi_16963_bounds.1]
  · change (16865630 : ℝ) / 1000 ≤ Chebyshev.theta (↑(17094 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 17094) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 17093) (b := 17094) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta16384_psi_17093_bounds.1]
  · change (16997327 : ℝ) / 1000 ≤ Chebyshev.theta (↑(17230 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 17230) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 17209) (b := 17230) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta16384_psi_17209_bounds.1]
  · change (17124173 : ℝ) / 1000 ≤ Chebyshev.theta (↑(17362 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 17362) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 17359) (b := 17362) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta16384_psi_17359_bounds.1]
  · change (17280132 : ℝ) / 1000 ≤ Chebyshev.theta (↑(17489 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 17489) (by norm_num only) (by norm_num only)
    linarith only [hd, theta16384_psi_17489_bounds.1]
  · change (17427079 : ℝ) / 1000 ≤ Chebyshev.theta (↑(17645 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 17645) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 17627) (b := 17645) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta16384_psi_17627_bounds.1]
  · change (17574026 : ℝ) / 1000 ≤ Chebyshev.theta (↑(17792 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 17792) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 17791) (b := 17792) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta16384_psi_17791_bounds.1]
  · change (17720280 : ℝ) / 1000 ≤ Chebyshev.theta (↑(17939 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 17939) (by norm_num only) (by norm_num only)
    linarith only [hd, theta16384_psi_17939_bounds.1]

/-- Every batch cell has a checked theta upper bound. -/
theorem theta16384_upper :
    ∀ r ∈ theta16384Cells, Chebyshev.theta (r.b - 1 : ℕ) ≤ (r.hi : ℝ) / 1000 := by
  intro r hr
  simp only [theta16384Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change Chebyshev.theta (↑(16546 : ℕ) : ℝ) ≤ (16544731 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 16546
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 16529) (b := 16546) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta16384_psi_16529_bounds.2]
  · change Chebyshev.theta (↑(16692 : ℕ) : ℝ) ≤ (16699996 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 16692
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 16691) (b := 16692) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta16384_psi_16691_bounds.2]
  · change Chebyshev.theta (↑(16847 : ℕ) : ℝ) ≤ (16838625 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 16847
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 16843) (b := 16847) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta16384_psi_16843_bounds.2]
  · change Chebyshev.theta (↑(16976 : ℕ) : ℝ) ≤ (16955074 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 16976
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 16963) (b := 16976) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta16384_psi_16963_bounds.2]
  · change Chebyshev.theta (↑(17093 : ℕ) : ℝ) ≤ (17091624 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 17093
    linarith only [hd, theta16384_psi_17093_bounds.2]
  · change Chebyshev.theta (↑(17229 : ℕ) : ℝ) ≤ (17223322 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 17229
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 17209) (b := 17229) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta16384_psi_17209_bounds.2]
  · change Chebyshev.theta (↑(17361 : ℕ) : ℝ) ≤ (17350168 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 17361
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 17359) (b := 17361) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta16384_psi_17359_bounds.2]
  · change Chebyshev.theta (↑(17488 : ℕ) : ℝ) ≤ (17496422 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 17488
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 17483) (b := 17488) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta16384_psi_17483_bounds.2]
  · change Chebyshev.theta (↑(17644 : ℕ) : ℝ) ≤ (17653073 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 17644
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 17627) (b := 17644) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta16384_psi_17627_bounds.2]
  · change Chebyshev.theta (↑(17791 : ℕ) : ℝ) ≤ (17800020 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 17791
    linarith only [hd, theta16384_psi_17791_bounds.2]
  · change Chebyshev.theta (↑(17938 : ℕ) : ℝ) ≤ (17936570 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 17938
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 17929) (b := 17938) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta16384_psi_17929_bounds.2]
  · change Chebyshev.theta (↑(18084 : ℕ) : ℝ) ≤ (18093915 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 18084
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 18077) (b := 18084) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta16384_psi_18077_bounds.2]

/-- The envelope bound applies at every cell a endpoint. -/
theorem theta16384_a :
    ∀ r ∈ theta16384Cells,
      (r.ca : ℝ) / 1000 ≤
        Real.sqrt r.a *
          (Real.log r.a * (Real.log r.a - Real.log (Real.log r.a)) / (8 * Real.pi)) := by
  intro r hr
  simp only [theta16384Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 16384 *
          (Real.log 16384 * (Real.log 16384 - Real.log (Real.log 16384)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 16547 *
          (Real.log 16547 * (Real.log 16547 - Real.log (Real.log 16547)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 16693 *
          (Real.log 16693 * (Real.log 16693 - Real.log (Real.log 16693)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 16848 *
          (Real.log 16848 * (Real.log 16848 - Real.log (Real.log 16848)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 16977 *
          (Real.log 16977 * (Real.log 16977 - Real.log (Real.log 16977)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 17094 *
          (Real.log 17094 * (Real.log 17094 - Real.log (Real.log 17094)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 17230 *
          (Real.log 17230 * (Real.log 17230 - Real.log (Real.log 17230)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 17362 *
          (Real.log 17362 * (Real.log 17362 - Real.log (Real.log 17362)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 17489 *
          (Real.log 17489 * (Real.log 17489 - Real.log (Real.log 17489)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 17645 *
          (Real.log 17645 * (Real.log 17645 - Real.log (Real.log 17645)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 17792 *
          (Real.log 17792 * (Real.log 17792 - Real.log (Real.log 17792)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 17939 *
          (Real.log 17939 * (Real.log 17939 - Real.log (Real.log 17939)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)

/-- The envelope bound applies at every cell b endpoint. -/
theorem theta16384_b :
    ∀ r ∈ theta16384Cells,
      (r.cb : ℝ) / 1000 ≤
        Real.sqrt r.b *
          (Real.log r.b * (Real.log r.b - Real.log (Real.log r.b)) / (8 * Real.pi)) := by
  intro r hr
  simp only [theta16384Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 16547 *
          (Real.log 16547 * (Real.log 16547 - Real.log (Real.log 16547)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 16693 *
          (Real.log 16693 * (Real.log 16693 - Real.log (Real.log 16693)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 16848 *
          (Real.log 16848 * (Real.log 16848 - Real.log (Real.log 16848)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 16977 *
          (Real.log 16977 * (Real.log 16977 - Real.log (Real.log 16977)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 17094 *
          (Real.log 17094 * (Real.log 17094 - Real.log (Real.log 17094)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 17230 *
          (Real.log 17230 * (Real.log 17230 - Real.log (Real.log 17230)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 17362 *
          (Real.log 17362 * (Real.log 17362 - Real.log (Real.log 17362)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 17489 *
          (Real.log 17489 * (Real.log 17489 - Real.log (Real.log 17489)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 17645 *
          (Real.log 17645 * (Real.log 17645 - Real.log (Real.log 17645)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 17792 *
          (Real.log 17792 * (Real.log 17792 - Real.log (Real.log 17792)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 17939 *
          (Real.log 17939 * (Real.log 17939 - Real.log (Real.log 17939)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 18085 *
          (Real.log 18085 * (Real.log 18085 - Real.log (Real.log 18085)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)

/-- The cells form a checked chain covering `[16384, 18085)`. -/
theorem theta16384_check : leeNosalChainCheck 16384 18085 theta16384Cells = true := by
  decide +kernel

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
