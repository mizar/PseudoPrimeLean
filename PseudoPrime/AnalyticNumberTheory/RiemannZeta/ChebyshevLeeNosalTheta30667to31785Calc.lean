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
def theta30667Cells : List LeeNosalCell :=
  [⟨30667, 30740, 30375761, 30684240, 365000, 365000⟩,
    ⟨30740, 30823, 30458246, 30756327, 365000, 365000⟩,
    ⟨30823, 30895, 30530333, 30859606, 365000, 365000⟩,
    ⟨30895, 30998, 30633612, 30942784, 365000, 365000⟩,
    ⟨30998, 31081, 30716790, 31025268, 365000, 365000⟩,
    ⟨31081, 31174, 30809671, 31118150, 365000, 365000⟩,
    ⟨31174, 31257, 30892156, 31242917, 365000, 365000⟩,
    ⟨31257, 31381, 31016922, 31366990, 365000, 365000⟩,
    ⟨31381, 31505, 31140996, 31449474, 365000, 365000⟩,
    ⟨31505, 31588, 31223480, 31553446, 365000, 365000⟩,
    ⟨31588, 31692, 31327452, 31646328, 365000, 365000⟩,
    ⟨31692, 31785, 31420334, 31739903, 365000, 365000⟩]

/-- The kernel-checked prefix bounds for 30661. -/
theorem theta30667_psi_30661_bounds :
    (30601061 : ℝ) / 1000 ≤ Chebyshev.psi 30661 ∧ Chebyshev.psi 30661 ≤ (30601755 : ℝ) / 1000 := by
  have hl : 2 ^ 44148 ≤ Nat.lcmUpto 30661 := by decide +kernel
  have hu : Nat.lcmUpto 30661 ≤ 2 ^ (44148 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 30727. -/
theorem theta30667_psi_30727_bounds :
    (30683546 : ℝ) / 1000 ≤ Chebyshev.psi 30727 ∧ Chebyshev.psi 30727 ≤ (30684240 : ℝ) / 1000 := by
  have hl : 2 ^ 44267 ≤ Nat.lcmUpto 30727 := by decide +kernel
  have hu : Nat.lcmUpto 30727 ≤ 2 ^ (44267 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 30817. -/
theorem theta30667_psi_30817_bounds :
    (30755633 : ℝ) / 1000 ≤ Chebyshev.psi 30817 ∧ Chebyshev.psi 30817 ≤ (30756327 : ℝ) / 1000 := by
  have hl : 2 ^ 44371 ≤ Nat.lcmUpto 30817 := by decide +kernel
  have hu : Nat.lcmUpto 30817 ≤ 2 ^ (44371 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 30893. -/
theorem theta30667_psi_30893_bounds :
    (30858912 : ℝ) / 1000 ≤ Chebyshev.psi 30893 ∧ Chebyshev.psi 30893 ≤ (30859606 : ℝ) / 1000 := by
  have hl : 2 ^ 44520 ≤ Nat.lcmUpto 30893 := by decide +kernel
  have hu : Nat.lcmUpto 30893 ≤ 2 ^ (44520 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 30983. -/
theorem theta30667_psi_30983_bounds :
    (30942090 : ℝ) / 1000 ≤ Chebyshev.psi 30983 ∧ Chebyshev.psi 30983 ≤ (30942784 : ℝ) / 1000 := by
  have hl : 2 ^ 44640 ≤ Nat.lcmUpto 30983 := by decide +kernel
  have hu : Nat.lcmUpto 30983 ≤ 2 ^ (44640 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 31079. -/
theorem theta30667_psi_31079_bounds :
    (31024574 : ℝ) / 1000 ≤ Chebyshev.psi 31079 ∧ Chebyshev.psi 31079 ≤ (31025268 : ℝ) / 1000 := by
  have hl : 2 ^ 44759 ≤ Nat.lcmUpto 31079 := by decide +kernel
  have hu : Nat.lcmUpto 31079 ≤ 2 ^ (44759 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 31081. -/
theorem theta30667_psi_31081_bounds :
    (31034971 : ℝ) / 1000 ≤ Chebyshev.psi 31081 ∧ Chebyshev.psi 31081 ≤ (31035666 : ℝ) / 1000 := by
  have hl : 2 ^ 44774 ≤ Nat.lcmUpto 31081 := by decide +kernel
  have hu : Nat.lcmUpto 31081 ≤ 2 ^ (44774 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 31159. -/
theorem theta30667_psi_31159_bounds :
    (31117456 : ℝ) / 1000 ≤ Chebyshev.psi 31159 ∧ Chebyshev.psi 31159 ≤ (31118150 : ℝ) / 1000 := by
  have hl : 2 ^ 44893 ≤ Nat.lcmUpto 31159 := by decide +kernel
  have hu : Nat.lcmUpto 31159 ≤ 2 ^ (44893 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 31253. -/
theorem theta30667_psi_31253_bounds :
    (31242222 : ℝ) / 1000 ≤ Chebyshev.psi 31253 ∧ Chebyshev.psi 31253 ≤ (31242917 : ℝ) / 1000 := by
  have hl : 2 ^ 45073 ≤ Nat.lcmUpto 31253 := by decide +kernel
  have hu : Nat.lcmUpto 31253 ≤ 2 ^ (45073 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 31379. -/
theorem theta30667_psi_31379_bounds :
    (31366296 : ℝ) / 1000 ≤ Chebyshev.psi 31379 ∧ Chebyshev.psi 31379 ≤ (31366990 : ℝ) / 1000 := by
  have hl : 2 ^ 45252 ≤ Nat.lcmUpto 31379 := by decide +kernel
  have hu : Nat.lcmUpto 31379 ≤ 2 ^ (45252 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 31489. -/
theorem theta30667_psi_31489_bounds :
    (31448780 : ℝ) / 1000 ≤ Chebyshev.psi 31489 ∧ Chebyshev.psi 31489 ≤ (31449474 : ℝ) / 1000 := by
  have hl : 2 ^ 45371 ≤ Nat.lcmUpto 31489 := by decide +kernel
  have hu : Nat.lcmUpto 31489 ≤ 2 ^ (45371 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 31583. -/
theorem theta30667_psi_31583_bounds :
    (31552752 : ℝ) / 1000 ≤ Chebyshev.psi 31583 ∧ Chebyshev.psi 31583 ≤ (31553446 : ℝ) / 1000 := by
  have hl : 2 ^ 45521 ≤ Nat.lcmUpto 31583 := by decide +kernel
  have hu : Nat.lcmUpto 31583 ≤ 2 ^ (45521 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 31687. -/
theorem theta30667_psi_31687_bounds :
    (31645634 : ℝ) / 1000 ≤ Chebyshev.psi 31687 ∧ Chebyshev.psi 31687 ≤ (31646328 : ℝ) / 1000 := by
  have hl : 2 ^ 45655 ≤ Nat.lcmUpto 31687 := by decide +kernel
  have hu : Nat.lcmUpto 31687 ≤ 2 ^ (45655 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 31771. -/
theorem theta30667_psi_31771_bounds :
    (31739209 : ℝ) / 1000 ≤ Chebyshev.psi 31771 ∧ Chebyshev.psi 31771 ≤ (31739903 : ℝ) / 1000 := by
  have hl : 2 ^ 45790 ≤ Nat.lcmUpto 31771 := by decide +kernel
  have hu : Nat.lcmUpto 31771 ≤ 2 ^ (45790 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- Every batch cell has a checked theta lower bound. -/
theorem theta30667_lower : ∀ r ∈ theta30667Cells, (r.lo : ℝ) / 1000 ≤ Chebyshev.theta r.a := by
  intro r hr
  simp only [theta30667Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change (30375761 : ℝ) / 1000 ≤ Chebyshev.theta (↑(30667 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 30667) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 30661) (b := 30667) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta30667_psi_30661_bounds.1]
  · change (30458246 : ℝ) / 1000 ≤ Chebyshev.theta (↑(30740 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 30740) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 30727) (b := 30740) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta30667_psi_30727_bounds.1]
  · change (30530333 : ℝ) / 1000 ≤ Chebyshev.theta (↑(30823 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 30823) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 30817) (b := 30823) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta30667_psi_30817_bounds.1]
  · change (30633612 : ℝ) / 1000 ≤ Chebyshev.theta (↑(30895 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 30895) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 30893) (b := 30895) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta30667_psi_30893_bounds.1]
  · change (30716790 : ℝ) / 1000 ≤ Chebyshev.theta (↑(30998 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 30998) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 30983) (b := 30998) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta30667_psi_30983_bounds.1]
  · change (30809671 : ℝ) / 1000 ≤ Chebyshev.theta (↑(31081 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 31081) (by norm_num only) (by norm_num only)
    linarith only [hd, theta30667_psi_31081_bounds.1]
  · change (30892156 : ℝ) / 1000 ≤ Chebyshev.theta (↑(31174 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 31174) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 31159) (b := 31174) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta30667_psi_31159_bounds.1]
  · change (31016922 : ℝ) / 1000 ≤ Chebyshev.theta (↑(31257 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 31257) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 31253) (b := 31257) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta30667_psi_31253_bounds.1]
  · change (31140996 : ℝ) / 1000 ≤ Chebyshev.theta (↑(31381 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 31381) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 31379) (b := 31381) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta30667_psi_31379_bounds.1]
  · change (31223480 : ℝ) / 1000 ≤ Chebyshev.theta (↑(31505 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 31505) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 31489) (b := 31505) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta30667_psi_31489_bounds.1]
  · change (31327452 : ℝ) / 1000 ≤ Chebyshev.theta (↑(31588 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 31588) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 31583) (b := 31588) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta30667_psi_31583_bounds.1]
  · change (31420334 : ℝ) / 1000 ≤ Chebyshev.theta (↑(31692 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 31692) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 31687) (b := 31692) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta30667_psi_31687_bounds.1]

/-- Every batch cell has a checked theta upper bound. -/
theorem theta30667_upper :
    ∀ r ∈ theta30667Cells, Chebyshev.theta (r.b - 1 : ℕ) ≤ (r.hi : ℝ) / 1000 := by
  intro r hr
  simp only [theta30667Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change Chebyshev.theta (↑(30739 : ℕ) : ℝ) ≤ (30684240 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 30739
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 30727) (b := 30739) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta30667_psi_30727_bounds.2]
  · change Chebyshev.theta (↑(30822 : ℕ) : ℝ) ≤ (30756327 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 30822
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 30817) (b := 30822) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta30667_psi_30817_bounds.2]
  · change Chebyshev.theta (↑(30894 : ℕ) : ℝ) ≤ (30859606 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 30894
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 30893) (b := 30894) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta30667_psi_30893_bounds.2]
  · change Chebyshev.theta (↑(30997 : ℕ) : ℝ) ≤ (30942784 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 30997
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 30983) (b := 30997) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta30667_psi_30983_bounds.2]
  · change Chebyshev.theta (↑(31080 : ℕ) : ℝ) ≤ (31025268 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 31080
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 31079) (b := 31080) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta30667_psi_31079_bounds.2]
  · change Chebyshev.theta (↑(31173 : ℕ) : ℝ) ≤ (31118150 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 31173
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 31159) (b := 31173) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta30667_psi_31159_bounds.2]
  · change Chebyshev.theta (↑(31256 : ℕ) : ℝ) ≤ (31242917 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 31256
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 31253) (b := 31256) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta30667_psi_31253_bounds.2]
  · change Chebyshev.theta (↑(31380 : ℕ) : ℝ) ≤ (31366990 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 31380
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 31379) (b := 31380) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta30667_psi_31379_bounds.2]
  · change Chebyshev.theta (↑(31504 : ℕ) : ℝ) ≤ (31449474 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 31504
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 31489) (b := 31504) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta30667_psi_31489_bounds.2]
  · change Chebyshev.theta (↑(31587 : ℕ) : ℝ) ≤ (31553446 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 31587
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 31583) (b := 31587) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta30667_psi_31583_bounds.2]
  · change Chebyshev.theta (↑(31691 : ℕ) : ℝ) ≤ (31646328 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 31691
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 31687) (b := 31691) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta30667_psi_31687_bounds.2]
  · change Chebyshev.theta (↑(31784 : ℕ) : ℝ) ≤ (31739903 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 31784
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 31771) (b := 31784) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta30667_psi_31771_bounds.2]

/-- The envelope bound applies at every cell a endpoint. -/
theorem theta30667_a :
    ∀ r ∈ theta30667Cells,
      (r.ca : ℝ) / 1000 ≤
        Real.sqrt r.a *
          (Real.log r.a * (Real.log r.a - Real.log (Real.log r.a)) / (8 * Real.pi)) := by
  intro r hr
  simp only [theta30667Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 30667 *
          (Real.log 30667 * (Real.log 30667 - Real.log (Real.log 30667)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 30740 *
          (Real.log 30740 * (Real.log 30740 - Real.log (Real.log 30740)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 30823 *
          (Real.log 30823 * (Real.log 30823 - Real.log (Real.log 30823)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 30895 *
          (Real.log 30895 * (Real.log 30895 - Real.log (Real.log 30895)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 30998 *
          (Real.log 30998 * (Real.log 30998 - Real.log (Real.log 30998)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 31081 *
          (Real.log 31081 * (Real.log 31081 - Real.log (Real.log 31081)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 31174 *
          (Real.log 31174 * (Real.log 31174 - Real.log (Real.log 31174)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 31257 *
          (Real.log 31257 * (Real.log 31257 - Real.log (Real.log 31257)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 31381 *
          (Real.log 31381 * (Real.log 31381 - Real.log (Real.log 31381)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 31505 *
          (Real.log 31505 * (Real.log 31505 - Real.log (Real.log 31505)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 31588 *
          (Real.log 31588 * (Real.log 31588 - Real.log (Real.log 31588)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 31692 *
          (Real.log 31692 * (Real.log 31692 - Real.log (Real.log 31692)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)

/-- The envelope bound applies at every cell b endpoint. -/
theorem theta30667_b :
    ∀ r ∈ theta30667Cells,
      (r.cb : ℝ) / 1000 ≤
        Real.sqrt r.b *
          (Real.log r.b * (Real.log r.b - Real.log (Real.log r.b)) / (8 * Real.pi)) := by
  intro r hr
  simp only [theta30667Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 30740 *
          (Real.log 30740 * (Real.log 30740 - Real.log (Real.log 30740)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 30823 *
          (Real.log 30823 * (Real.log 30823 - Real.log (Real.log 30823)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 30895 *
          (Real.log 30895 * (Real.log 30895 - Real.log (Real.log 30895)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 30998 *
          (Real.log 30998 * (Real.log 30998 - Real.log (Real.log 30998)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 31081 *
          (Real.log 31081 * (Real.log 31081 - Real.log (Real.log 31081)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 31174 *
          (Real.log 31174 * (Real.log 31174 - Real.log (Real.log 31174)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 31257 *
          (Real.log 31257 * (Real.log 31257 - Real.log (Real.log 31257)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 31381 *
          (Real.log 31381 * (Real.log 31381 - Real.log (Real.log 31381)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 31505 *
          (Real.log 31505 * (Real.log 31505 - Real.log (Real.log 31505)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 31588 *
          (Real.log 31588 * (Real.log 31588 - Real.log (Real.log 31588)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 31692 *
          (Real.log 31692 * (Real.log 31692 - Real.log (Real.log 31692)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 31785 *
          (Real.log 31785 * (Real.log 31785 - Real.log (Real.log 31785)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)

/-- The cells form a checked chain covering `[30667, 31785)`. -/
theorem theta30667_check : leeNosalChainCheck 30667 31785 theta30667Cells = true := by
  decide +kernel

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
