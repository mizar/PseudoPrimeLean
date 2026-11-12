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
def theta11287Cells : List LeeNosalCell :=
  [⟨11287, 11379, 11124989, 11358603, 255000, 255000⟩,
    ⟨11379, 11454, 11199849, 11438315, 255000, 255000⟩,
    ⟨11454, 11534, 11279561, 11522186, 255000, 255000⟩,
    ⟨11534, 11618, 11363432, 11587342, 255000, 255000⟩,
    ⟨11618, 11683, 11428588, 11634476, 255000, 255000⟩,
    ⟨11683, 11730, 11475722, 11681610, 255000, 255000⟩,
    ⟨11730, 11777, 11522856, 11700325, 255000, 255000⟩,
    ⟨11777, 11805, 11550582, 11746766, 255000, 255000⟩,
    ⟨11805, 11843, 11588012, 11812615, 255000, 255000⟩,
    ⟨11843, 11908, 11653861, 11863908, 255000, 255000⟩,
    ⟨11908, 11960, 11705153, 11939461, 255000, 255000⟩,
    ⟨11960, 12035, 11780707, 11995606, 255000, 255000⟩]

/-- The kernel-checked prefix bounds for 11287. -/
theorem theta11287_psi_11287_bounds :
    (11283049 : ℝ) / 1000 ≤ Chebyshev.psi 11287 ∧ Chebyshev.psi 11287 ≤ (11283743 : ℝ) / 1000 := by
  have hl : 2 ^ 16278 ≤ Nat.lcmUpto 11287 := by decide +kernel
  have hu : Nat.lcmUpto 11287 ≤ 2 ^ (16278 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 11369. -/
theorem theta11287_psi_11369_bounds :
    (11357909 : ℝ) / 1000 ≤ Chebyshev.psi 11369 ∧ Chebyshev.psi 11369 ≤ (11358603 : ℝ) / 1000 := by
  have hl : 2 ^ 16386 ≤ Nat.lcmUpto 11369 := by decide +kernel
  have hu : Nat.lcmUpto 11369 ≤ 2 ^ (16386 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 11449. -/
theorem theta11287_psi_11449_bounds :
    (11437621 : ℝ) / 1000 ≤ Chebyshev.psi 11449 ∧ Chebyshev.psi 11449 ≤ (11438315 : ℝ) / 1000 := by
  have hl : 2 ^ 16501 ≤ Nat.lcmUpto 11449 := by decide +kernel
  have hu : Nat.lcmUpto 11449 ≤ 2 ^ (16501 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 11527. -/
theorem theta11287_psi_11527_bounds :
    (11521492 : ℝ) / 1000 ≤ Chebyshev.psi 11527 ∧ Chebyshev.psi 11527 ≤ (11522186 : ℝ) / 1000 := by
  have hl : 2 ^ 16622 ≤ Nat.lcmUpto 11527 := by decide +kernel
  have hu : Nat.lcmUpto 11527 ≤ 2 ^ (16622 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 11617. -/
theorem theta11287_psi_11617_bounds :
    (11586648 : ℝ) / 1000 ≤ Chebyshev.psi 11617 ∧ Chebyshev.psi 11617 ≤ (11587342 : ℝ) / 1000 := by
  have hl : 2 ^ 16716 ≤ Nat.lcmUpto 11617 := by decide +kernel
  have hu : Nat.lcmUpto 11617 ≤ 2 ^ (16716 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 11681. -/
theorem theta11287_psi_11681_bounds :
    (11633782 : ℝ) / 1000 ≤ Chebyshev.psi 11681 ∧ Chebyshev.psi 11681 ≤ (11634476 : ℝ) / 1000 := by
  have hl : 2 ^ 16784 ≤ Nat.lcmUpto 11681 := by decide +kernel
  have hu : Nat.lcmUpto 11681 ≤ 2 ^ (16784 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 11719. -/
theorem theta11287_psi_11719_bounds :
    (11680916 : ℝ) / 1000 ≤ Chebyshev.psi 11719 ∧ Chebyshev.psi 11719 ≤ (11681610 : ℝ) / 1000 := by
  have hl : 2 ^ 16852 ≤ Nat.lcmUpto 11719 := by decide +kernel
  have hu : Nat.lcmUpto 11719 ≤ 2 ^ (16852 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 11743. -/
theorem theta11287_psi_11743_bounds :
    (11699631 : ℝ) / 1000 ≤ Chebyshev.psi 11743 ∧ Chebyshev.psi 11743 ≤ (11700325 : ℝ) / 1000 := by
  have hl : 2 ^ 16879 ≤ Nat.lcmUpto 11743 := by decide +kernel
  have hu : Nat.lcmUpto 11743 ≤ 2 ^ (16879 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 11777. -/
theorem theta11287_psi_11777_bounds :
    (11708642 : ℝ) / 1000 ≤ Chebyshev.psi 11777 ∧ Chebyshev.psi 11777 ≤ (11709336 : ℝ) / 1000 := by
  have hl : 2 ^ 16892 ≤ Nat.lcmUpto 11777 := by decide +kernel
  have hu : Nat.lcmUpto 11777 ≤ 2 ^ (16892 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 11801. -/
theorem theta11287_psi_11801_bounds :
    (11746072 : ℝ) / 1000 ≤ Chebyshev.psi 11801 ∧ Chebyshev.psi 11801 ≤ (11746766 : ℝ) / 1000 := by
  have hl : 2 ^ 16946 ≤ Nat.lcmUpto 11801 := by decide +kernel
  have hu : Nat.lcmUpto 11801 ≤ 2 ^ (16946 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 11839. -/
theorem theta11287_psi_11839_bounds :
    (11811921 : ℝ) / 1000 ≤ Chebyshev.psi 11839 ∧ Chebyshev.psi 11839 ≤ (11812615 : ℝ) / 1000 := by
  have hl : 2 ^ 17041 ≤ Nat.lcmUpto 11839 := by decide +kernel
  have hu : Nat.lcmUpto 11839 ≤ 2 ^ (17041 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 11903. -/
theorem theta11287_psi_11903_bounds :
    (11863213 : ℝ) / 1000 ≤ Chebyshev.psi 11903 ∧ Chebyshev.psi 11903 ≤ (11863908 : ℝ) / 1000 := by
  have hl : 2 ^ 17115 ≤ Nat.lcmUpto 11903 := by decide +kernel
  have hu : Nat.lcmUpto 11903 ≤ 2 ^ (17115 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 11959. -/
theorem theta11287_psi_11959_bounds :
    (11938767 : ℝ) / 1000 ≤ Chebyshev.psi 11959 ∧ Chebyshev.psi 11959 ≤ (11939461 : ℝ) / 1000 := by
  have hl : 2 ^ 17224 ≤ Nat.lcmUpto 11959 := by decide +kernel
  have hu : Nat.lcmUpto 11959 ≤ 2 ^ (17224 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 12011. -/
theorem theta11287_psi_12011_bounds :
    (11994911 : ℝ) / 1000 ≤ Chebyshev.psi 12011 ∧ Chebyshev.psi 12011 ≤ (11995606 : ℝ) / 1000 := by
  have hl : 2 ^ 17305 ≤ Nat.lcmUpto 12011 := by decide +kernel
  have hu : Nat.lcmUpto 12011 ≤ 2 ^ (17305 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- Every batch cell has a checked theta lower bound. -/
theorem theta11287_lower : ∀ r ∈ theta11287Cells, (r.lo : ℝ) / 1000 ≤ Chebyshev.theta r.a := by
  intro r hr
  simp only [theta11287Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change (11124989 : ℝ) / 1000 ≤ Chebyshev.theta (↑(11287 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 11287) (by norm_num only) (by norm_num only)
    linarith only [hd, theta11287_psi_11287_bounds.1]
  · change (11199849 : ℝ) / 1000 ≤ Chebyshev.theta (↑(11379 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 11379) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 11369) (b := 11379) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta11287_psi_11369_bounds.1]
  · change (11279561 : ℝ) / 1000 ≤ Chebyshev.theta (↑(11454 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 11454) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 11449) (b := 11454) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta11287_psi_11449_bounds.1]
  · change (11363432 : ℝ) / 1000 ≤ Chebyshev.theta (↑(11534 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 11534) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 11527) (b := 11534) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta11287_psi_11527_bounds.1]
  · change (11428588 : ℝ) / 1000 ≤ Chebyshev.theta (↑(11618 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 11618) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 11617) (b := 11618) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta11287_psi_11617_bounds.1]
  · change (11475722 : ℝ) / 1000 ≤ Chebyshev.theta (↑(11683 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 11683) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 11681) (b := 11683) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta11287_psi_11681_bounds.1]
  · change (11522856 : ℝ) / 1000 ≤ Chebyshev.theta (↑(11730 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 11730) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 11719) (b := 11730) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta11287_psi_11719_bounds.1]
  · change (11550582 : ℝ) / 1000 ≤ Chebyshev.theta (↑(11777 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 11777) (by norm_num only) (by norm_num only)
    linarith only [hd, theta11287_psi_11777_bounds.1]
  · change (11588012 : ℝ) / 1000 ≤ Chebyshev.theta (↑(11805 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 11805) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 11801) (b := 11805) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta11287_psi_11801_bounds.1]
  · change (11653861 : ℝ) / 1000 ≤ Chebyshev.theta (↑(11843 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 11843) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 11839) (b := 11843) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta11287_psi_11839_bounds.1]
  · change (11705153 : ℝ) / 1000 ≤ Chebyshev.theta (↑(11908 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 11908) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 11903) (b := 11908) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta11287_psi_11903_bounds.1]
  · change (11780707 : ℝ) / 1000 ≤ Chebyshev.theta (↑(11960 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 11960) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 11959) (b := 11960) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta11287_psi_11959_bounds.1]

/-- Every batch cell has a checked theta upper bound. -/
theorem theta11287_upper :
    ∀ r ∈ theta11287Cells, Chebyshev.theta (r.b - 1 : ℕ) ≤ (r.hi : ℝ) / 1000 := by
  intro r hr
  simp only [theta11287Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change Chebyshev.theta (↑(11378 : ℕ) : ℝ) ≤ (11358603 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 11378
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 11369) (b := 11378) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta11287_psi_11369_bounds.2]
  · change Chebyshev.theta (↑(11453 : ℕ) : ℝ) ≤ (11438315 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 11453
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 11449) (b := 11453) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta11287_psi_11449_bounds.2]
  · change Chebyshev.theta (↑(11533 : ℕ) : ℝ) ≤ (11522186 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 11533
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 11527) (b := 11533) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta11287_psi_11527_bounds.2]
  · change Chebyshev.theta (↑(11617 : ℕ) : ℝ) ≤ (11587342 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 11617
    linarith only [hd, theta11287_psi_11617_bounds.2]
  · change Chebyshev.theta (↑(11682 : ℕ) : ℝ) ≤ (11634476 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 11682
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 11681) (b := 11682) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta11287_psi_11681_bounds.2]
  · change Chebyshev.theta (↑(11729 : ℕ) : ℝ) ≤ (11681610 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 11729
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 11719) (b := 11729) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta11287_psi_11719_bounds.2]
  · change Chebyshev.theta (↑(11776 : ℕ) : ℝ) ≤ (11700325 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 11776
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 11743) (b := 11776) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta11287_psi_11743_bounds.2]
  · change Chebyshev.theta (↑(11804 : ℕ) : ℝ) ≤ (11746766 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 11804
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 11801) (b := 11804) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta11287_psi_11801_bounds.2]
  · change Chebyshev.theta (↑(11842 : ℕ) : ℝ) ≤ (11812615 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 11842
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 11839) (b := 11842) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta11287_psi_11839_bounds.2]
  · change Chebyshev.theta (↑(11907 : ℕ) : ℝ) ≤ (11863908 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 11907
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 11903) (b := 11907) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta11287_psi_11903_bounds.2]
  · change Chebyshev.theta (↑(11959 : ℕ) : ℝ) ≤ (11939461 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 11959
    linarith only [hd, theta11287_psi_11959_bounds.2]
  · change Chebyshev.theta (↑(12034 : ℕ) : ℝ) ≤ (11995606 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 12034
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 12011) (b := 12034) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta11287_psi_12011_bounds.2]

/-- The envelope bound applies at every cell a endpoint. -/
theorem theta11287_a :
    ∀ r ∈ theta11287Cells,
      (r.ca : ℝ) / 1000 ≤
        Real.sqrt r.a *
          (Real.log r.a * (Real.log r.a - Real.log (Real.log r.a)) / (8 * Real.pi)) := by
  intro r hr
  simp only [theta11287Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 11287 *
          (Real.log 11287 * (Real.log 11287 - Real.log (Real.log 11287)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 11379 *
          (Real.log 11379 * (Real.log 11379 - Real.log (Real.log 11379)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 11454 *
          (Real.log 11454 * (Real.log 11454 - Real.log (Real.log 11454)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 11534 *
          (Real.log 11534 * (Real.log 11534 - Real.log (Real.log 11534)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 11618 *
          (Real.log 11618 * (Real.log 11618 - Real.log (Real.log 11618)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 11683 *
          (Real.log 11683 * (Real.log 11683 - Real.log (Real.log 11683)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 11730 *
          (Real.log 11730 * (Real.log 11730 - Real.log (Real.log 11730)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 11777 *
          (Real.log 11777 * (Real.log 11777 - Real.log (Real.log 11777)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 11805 *
          (Real.log 11805 * (Real.log 11805 - Real.log (Real.log 11805)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 11843 *
          (Real.log 11843 * (Real.log 11843 - Real.log (Real.log 11843)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 11908 *
          (Real.log 11908 * (Real.log 11908 - Real.log (Real.log 11908)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 11960 *
          (Real.log 11960 * (Real.log 11960 - Real.log (Real.log 11960)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)

/-- The envelope bound applies at every cell b endpoint. -/
theorem theta11287_b :
    ∀ r ∈ theta11287Cells,
      (r.cb : ℝ) / 1000 ≤
        Real.sqrt r.b *
          (Real.log r.b * (Real.log r.b - Real.log (Real.log r.b)) / (8 * Real.pi)) := by
  intro r hr
  simp only [theta11287Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 11379 *
          (Real.log 11379 * (Real.log 11379 - Real.log (Real.log 11379)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 11454 *
          (Real.log 11454 * (Real.log 11454 - Real.log (Real.log 11454)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 11534 *
          (Real.log 11534 * (Real.log 11534 - Real.log (Real.log 11534)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 11618 *
          (Real.log 11618 * (Real.log 11618 - Real.log (Real.log 11618)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 11683 *
          (Real.log 11683 * (Real.log 11683 - Real.log (Real.log 11683)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 11730 *
          (Real.log 11730 * (Real.log 11730 - Real.log (Real.log 11730)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 11777 *
          (Real.log 11777 * (Real.log 11777 - Real.log (Real.log 11777)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 11805 *
          (Real.log 11805 * (Real.log 11805 - Real.log (Real.log 11805)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 11843 *
          (Real.log 11843 * (Real.log 11843 - Real.log (Real.log 11843)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 11908 *
          (Real.log 11908 * (Real.log 11908 - Real.log (Real.log 11908)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 11960 *
          (Real.log 11960 * (Real.log 11960 - Real.log (Real.log 11960)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 12035 *
          (Real.log 12035 * (Real.log 12035 - Real.log (Real.log 12035)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)

/-- The cells form a checked chain covering `[11287, 12035)`. -/
theorem theta11287_check : leeNosalChainCheck 11287 12035 theta11287Cells = true := by
  decide +kernel

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
