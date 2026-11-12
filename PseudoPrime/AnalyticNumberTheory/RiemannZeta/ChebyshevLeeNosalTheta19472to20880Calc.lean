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
def theta19472Cells : List LeeNosalCell :=
  [⟨19472, 19590, 19225796, 19580022, 365000, 365000⟩,
    ⟨19590, 19719, 19354028, 19679835, 365000, 365000⟩,
    ⟨19719, 19818, 19453841, 19778955, 365000, 365000⟩,
    ⟨19818, 19917, 19552961, 19867678, 365000, 365000⟩,
    ⟨19917, 20006, 19641684, 19977195, 365000, 365000⟩,
    ⟨20006, 20116, 19751201, 20095724, 365000, 365000⟩,
    ⟨20116, 20234, 19869729, 20234353, 365000, 365000⟩,
    ⟨20234, 20373, 20008359, 20373676, 365000, 365000⟩,
    ⟨20373, 20512, 20147681, 20502601, 365000, 365000⟩,
    ⟨20512, 20641, 20276607, 20611425, 365000, 365000⟩,
    ⟨20641, 20760, 20395828, 20741044, 365000, 365000⟩,
    ⟨20760, 20880, 20515049, 20830460, 365000, 365000⟩]

/-- The kernel-checked prefix bounds for 19471. -/
theorem theta19472_psi_19471_bounds :
    (19451096 : ℝ) / 1000 ≤ Chebyshev.psi 19471 ∧ Chebyshev.psi 19471 ≤ (19451790 : ℝ) / 1000 := by
  have hl : 2 ^ 28062 ≤ Nat.lcmUpto 19471 := by decide +kernel
  have hu : Nat.lcmUpto 19471 ≤ 2 ^ (28062 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 19583. -/
theorem theta19472_psi_19583_bounds :
    (19579328 : ℝ) / 1000 ≤ Chebyshev.psi 19583 ∧ Chebyshev.psi 19583 ≤ (19580022 : ℝ) / 1000 := by
  have hl : 2 ^ 28247 ≤ Nat.lcmUpto 19583 := by decide +kernel
  have hu : Nat.lcmUpto 19583 ≤ 2 ^ (28247 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 19717. -/
theorem theta19472_psi_19717_bounds :
    (19679141 : ℝ) / 1000 ≤ Chebyshev.psi 19717 ∧ Chebyshev.psi 19717 ≤ (19679835 : ℝ) / 1000 := by
  have hl : 2 ^ 28391 ≤ Nat.lcmUpto 19717 := by decide +kernel
  have hu : Nat.lcmUpto 19717 ≤ 2 ^ (28391 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 19813. -/
theorem theta19472_psi_19813_bounds :
    (19778261 : ℝ) / 1000 ≤ Chebyshev.psi 19813 ∧ Chebyshev.psi 19813 ≤ (19778955 : ℝ) / 1000 := by
  have hl : 2 ^ 28534 ≤ Nat.lcmUpto 19813 := by decide +kernel
  have hu : Nat.lcmUpto 19813 ≤ 2 ^ (28534 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 19913. -/
theorem theta19472_psi_19913_bounds :
    (19866984 : ℝ) / 1000 ≤ Chebyshev.psi 19913 ∧ Chebyshev.psi 19913 ≤ (19867678 : ℝ) / 1000 := by
  have hl : 2 ^ 28662 ≤ Nat.lcmUpto 19913 := by decide +kernel
  have hu : Nat.lcmUpto 19913 ≤ 2 ^ (28662 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 19997. -/
theorem theta19472_psi_19997_bounds :
    (19976501 : ℝ) / 1000 ≤ Chebyshev.psi 19997 ∧ Chebyshev.psi 19997 ≤ (19977195 : ℝ) / 1000 := by
  have hl : 2 ^ 28820 ≤ Nat.lcmUpto 19997 := by decide +kernel
  have hu : Nat.lcmUpto 19997 ≤ 2 ^ (28820 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 20113. -/
theorem theta19472_psi_20113_bounds :
    (20095029 : ℝ) / 1000 ≤ Chebyshev.psi 20113 ∧ Chebyshev.psi 20113 ≤ (20095724 : ℝ) / 1000 := by
  have hl : 2 ^ 28991 ≤ Nat.lcmUpto 20113 := by decide +kernel
  have hu : Nat.lcmUpto 20113 ≤ 2 ^ (28991 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 20233. -/
theorem theta19472_psi_20233_bounds :
    (20233659 : ℝ) / 1000 ≤ Chebyshev.psi 20233 ∧ Chebyshev.psi 20233 ≤ (20234353 : ℝ) / 1000 := by
  have hl : 2 ^ 29191 ≤ Nat.lcmUpto 20233 := by decide +kernel
  have hu : Nat.lcmUpto 20233 ≤ 2 ^ (29191 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 20369. -/
theorem theta19472_psi_20369_bounds :
    (20372981 : ℝ) / 1000 ≤ Chebyshev.psi 20369 ∧ Chebyshev.psi 20369 ≤ (20373676 : ℝ) / 1000 := by
  have hl : 2 ^ 29392 ≤ Nat.lcmUpto 20369 := by decide +kernel
  have hu : Nat.lcmUpto 20369 ≤ 2 ^ (29392 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 20509. -/
theorem theta19472_psi_20509_bounds :
    (20501907 : ℝ) / 1000 ≤ Chebyshev.psi 20509 ∧ Chebyshev.psi 20509 ≤ (20502601 : ℝ) / 1000 := by
  have hl : 2 ^ 29578 ≤ Nat.lcmUpto 20509 := by decide +kernel
  have hu : Nat.lcmUpto 20509 ≤ 2 ^ (29578 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 20639. -/
theorem theta19472_psi_20639_bounds :
    (20610731 : ℝ) / 1000 ≤ Chebyshev.psi 20639 ∧ Chebyshev.psi 20639 ≤ (20611425 : ℝ) / 1000 := by
  have hl : 2 ^ 29735 ≤ Nat.lcmUpto 20639 := by decide +kernel
  have hu : Nat.lcmUpto 20639 ≤ 2 ^ (29735 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 20641. -/
theorem theta19472_psi_20641_bounds :
    (20621128 : ℝ) / 1000 ≤ Chebyshev.psi 20641 ∧ Chebyshev.psi 20641 ≤ (20621822 : ℝ) / 1000 := by
  have hl : 2 ^ 29750 ≤ Nat.lcmUpto 20641 := by decide +kernel
  have hu : Nat.lcmUpto 20641 ≤ 2 ^ (29750 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 20759. -/
theorem theta19472_psi_20759_bounds :
    (20740349 : ℝ) / 1000 ≤ Chebyshev.psi 20759 ∧ Chebyshev.psi 20759 ≤ (20741044 : ℝ) / 1000 := by
  have hl : 2 ^ 29922 ≤ Nat.lcmUpto 20759 := by decide +kernel
  have hu : Nat.lcmUpto 20759 ≤ 2 ^ (29922 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 20879. -/
theorem theta19472_psi_20879_bounds :
    (20829765 : ℝ) / 1000 ≤ Chebyshev.psi 20879 ∧ Chebyshev.psi 20879 ≤ (20830460 : ℝ) / 1000 := by
  have hl : 2 ^ 30051 ≤ Nat.lcmUpto 20879 := by decide +kernel
  have hu : Nat.lcmUpto 20879 ≤ 2 ^ (30051 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- Every batch cell has a checked theta lower bound. -/
theorem theta19472_lower : ∀ r ∈ theta19472Cells, (r.lo : ℝ) / 1000 ≤ Chebyshev.theta r.a := by
  intro r hr
  simp only [theta19472Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change (19225796 : ℝ) / 1000 ≤ Chebyshev.theta (↑(19472 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 19472) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 19471) (b := 19472) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta19472_psi_19471_bounds.1]
  · change (19354028 : ℝ) / 1000 ≤ Chebyshev.theta (↑(19590 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 19590) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 19583) (b := 19590) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta19472_psi_19583_bounds.1]
  · change (19453841 : ℝ) / 1000 ≤ Chebyshev.theta (↑(19719 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 19719) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 19717) (b := 19719) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta19472_psi_19717_bounds.1]
  · change (19552961 : ℝ) / 1000 ≤ Chebyshev.theta (↑(19818 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 19818) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 19813) (b := 19818) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta19472_psi_19813_bounds.1]
  · change (19641684 : ℝ) / 1000 ≤ Chebyshev.theta (↑(19917 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 19917) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 19913) (b := 19917) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta19472_psi_19913_bounds.1]
  · change (19751201 : ℝ) / 1000 ≤ Chebyshev.theta (↑(20006 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 20006) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 19997) (b := 20006) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta19472_psi_19997_bounds.1]
  · change (19869729 : ℝ) / 1000 ≤ Chebyshev.theta (↑(20116 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 20116) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 20113) (b := 20116) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta19472_psi_20113_bounds.1]
  · change (20008359 : ℝ) / 1000 ≤ Chebyshev.theta (↑(20234 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 20234) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 20233) (b := 20234) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta19472_psi_20233_bounds.1]
  · change (20147681 : ℝ) / 1000 ≤ Chebyshev.theta (↑(20373 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 20373) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 20369) (b := 20373) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta19472_psi_20369_bounds.1]
  · change (20276607 : ℝ) / 1000 ≤ Chebyshev.theta (↑(20512 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 20512) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 20509) (b := 20512) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta19472_psi_20509_bounds.1]
  · change (20395828 : ℝ) / 1000 ≤ Chebyshev.theta (↑(20641 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 20641) (by norm_num only) (by norm_num only)
    linarith only [hd, theta19472_psi_20641_bounds.1]
  · change (20515049 : ℝ) / 1000 ≤ Chebyshev.theta (↑(20760 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 20760) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 20759) (b := 20760) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta19472_psi_20759_bounds.1]

/-- Every batch cell has a checked theta upper bound. -/
theorem theta19472_upper :
    ∀ r ∈ theta19472Cells, Chebyshev.theta (r.b - 1 : ℕ) ≤ (r.hi : ℝ) / 1000 := by
  intro r hr
  simp only [theta19472Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change Chebyshev.theta (↑(19589 : ℕ) : ℝ) ≤ (19580022 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 19589
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 19583) (b := 19589) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta19472_psi_19583_bounds.2]
  · change Chebyshev.theta (↑(19718 : ℕ) : ℝ) ≤ (19679835 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 19718
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 19717) (b := 19718) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta19472_psi_19717_bounds.2]
  · change Chebyshev.theta (↑(19817 : ℕ) : ℝ) ≤ (19778955 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 19817
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 19813) (b := 19817) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta19472_psi_19813_bounds.2]
  · change Chebyshev.theta (↑(19916 : ℕ) : ℝ) ≤ (19867678 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 19916
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 19913) (b := 19916) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta19472_psi_19913_bounds.2]
  · change Chebyshev.theta (↑(20005 : ℕ) : ℝ) ≤ (19977195 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 20005
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 19997) (b := 20005) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta19472_psi_19997_bounds.2]
  · change Chebyshev.theta (↑(20115 : ℕ) : ℝ) ≤ (20095724 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 20115
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 20113) (b := 20115) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta19472_psi_20113_bounds.2]
  · change Chebyshev.theta (↑(20233 : ℕ) : ℝ) ≤ (20234353 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 20233
    linarith only [hd, theta19472_psi_20233_bounds.2]
  · change Chebyshev.theta (↑(20372 : ℕ) : ℝ) ≤ (20373676 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 20372
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 20369) (b := 20372) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta19472_psi_20369_bounds.2]
  · change Chebyshev.theta (↑(20511 : ℕ) : ℝ) ≤ (20502601 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 20511
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 20509) (b := 20511) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta19472_psi_20509_bounds.2]
  · change Chebyshev.theta (↑(20640 : ℕ) : ℝ) ≤ (20611425 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 20640
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 20639) (b := 20640) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta19472_psi_20639_bounds.2]
  · change Chebyshev.theta (↑(20759 : ℕ) : ℝ) ≤ (20741044 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 20759
    linarith only [hd, theta19472_psi_20759_bounds.2]
  · change Chebyshev.theta (↑(20879 : ℕ) : ℝ) ≤ (20830460 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 20879
    linarith only [hd, theta19472_psi_20879_bounds.2]

/-- The envelope bound applies at every cell a endpoint. -/
theorem theta19472_a :
    ∀ r ∈ theta19472Cells,
      (r.ca : ℝ) / 1000 ≤
        Real.sqrt r.a *
          (Real.log r.a * (Real.log r.a - Real.log (Real.log r.a)) / (8 * Real.pi)) := by
  intro r hr
  simp only [theta19472Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 19472 *
          (Real.log 19472 * (Real.log 19472 - Real.log (Real.log 19472)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 19590 *
          (Real.log 19590 * (Real.log 19590 - Real.log (Real.log 19590)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 19719 *
          (Real.log 19719 * (Real.log 19719 - Real.log (Real.log 19719)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 19818 *
          (Real.log 19818 * (Real.log 19818 - Real.log (Real.log 19818)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 19917 *
          (Real.log 19917 * (Real.log 19917 - Real.log (Real.log 19917)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 20006 *
          (Real.log 20006 * (Real.log 20006 - Real.log (Real.log 20006)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 20116 *
          (Real.log 20116 * (Real.log 20116 - Real.log (Real.log 20116)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 20234 *
          (Real.log 20234 * (Real.log 20234 - Real.log (Real.log 20234)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 20373 *
          (Real.log 20373 * (Real.log 20373 - Real.log (Real.log 20373)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 20512 *
          (Real.log 20512 * (Real.log 20512 - Real.log (Real.log 20512)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 20641 *
          (Real.log 20641 * (Real.log 20641 - Real.log (Real.log 20641)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 20760 *
          (Real.log 20760 * (Real.log 20760 - Real.log (Real.log 20760)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)

/-- The envelope bound applies at every cell b endpoint. -/
theorem theta19472_b :
    ∀ r ∈ theta19472Cells,
      (r.cb : ℝ) / 1000 ≤
        Real.sqrt r.b *
          (Real.log r.b * (Real.log r.b - Real.log (Real.log r.b)) / (8 * Real.pi)) := by
  intro r hr
  simp only [theta19472Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 19590 *
          (Real.log 19590 * (Real.log 19590 - Real.log (Real.log 19590)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 19719 *
          (Real.log 19719 * (Real.log 19719 - Real.log (Real.log 19719)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 19818 *
          (Real.log 19818 * (Real.log 19818 - Real.log (Real.log 19818)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 19917 *
          (Real.log 19917 * (Real.log 19917 - Real.log (Real.log 19917)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 20006 *
          (Real.log 20006 * (Real.log 20006 - Real.log (Real.log 20006)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 20116 *
          (Real.log 20116 * (Real.log 20116 - Real.log (Real.log 20116)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 20234 *
          (Real.log 20234 * (Real.log 20234 - Real.log (Real.log 20234)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 20373 *
          (Real.log 20373 * (Real.log 20373 - Real.log (Real.log 20373)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 20512 *
          (Real.log 20512 * (Real.log 20512 - Real.log (Real.log 20512)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 20641 *
          (Real.log 20641 * (Real.log 20641 - Real.log (Real.log 20641)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 20760 *
          (Real.log 20760 * (Real.log 20760 - Real.log (Real.log 20760)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 20880 *
          (Real.log 20880 * (Real.log 20880 - Real.log (Real.log 20880)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)

/-- The cells form a checked chain covering `[19472, 20880)`. -/
theorem theta19472_check : leeNosalChainCheck 19472 20880 theta19472Cells = true := by
  decide +kernel

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
