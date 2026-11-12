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
def theta29176Cells : List LeeNosalCell :=
  [⟨29176, 29330, 28965207, 29345773, 365000, 365000⟩,
    ⟨29330, 29484, 29119779, 29520446, 365000, 365000⟩,
    ⟨29484, 29659, 29294452, 29664620, 365000, 365000⟩,
    ⟨29659, 29803, 29438626, 29781069, 365000, 365000⟩,
    ⟨29803, 29930, 29565472, 29920392, 365000, 365000⟩,
    ⟨29930, 30059, 29694398, 30002876, 365000, 365000⟩,
    ⟨30059, 30152, 29787279, 30126950, 365000, 365000⟩,
    ⟨30152, 30265, 29900955, 30239933, 365000, 365000⟩,
    ⟨30265, 30378, 30013938, 30343211, 365000, 365000⟩,
    ⟨30378, 30482, 30117217, 30425696, 365000, 365000⟩,
    ⟨30482, 30564, 30199702, 30528975, 365000, 365000⟩,
    ⟨30564, 30667, 30302981, 30601755, 365000, 365000⟩]

/-- The kernel-checked prefix bounds for 29173. -/
theorem theta29176_psi_29173_bounds :
    (29190507 : ℝ) / 1000 ≤ Chebyshev.psi 29173 ∧ Chebyshev.psi 29173 ≤ (29191201 : ℝ) / 1000 := by
  have hl : 2 ^ 42113 ≤ Nat.lcmUpto 29173 := by decide +kernel
  have hu : Nat.lcmUpto 29173 ≤ 2 ^ (42113 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 29327. -/
theorem theta29176_psi_29327_bounds :
    (29345079 : ℝ) / 1000 ≤ Chebyshev.psi 29327 ∧ Chebyshev.psi 29327 ≤ (29345773 : ℝ) / 1000 := by
  have hl : 2 ^ 42336 ≤ Nat.lcmUpto 29327 := by decide +kernel
  have hu : Nat.lcmUpto 29327 ≤ 2 ^ (42336 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 29483. -/
theorem theta29176_psi_29483_bounds :
    (29519752 : ℝ) / 1000 ≤ Chebyshev.psi 29483 ∧ Chebyshev.psi 29483 ≤ (29520446 : ℝ) / 1000 := by
  have hl : 2 ^ 42588 ≤ Nat.lcmUpto 29483 := by decide +kernel
  have hu : Nat.lcmUpto 29483 ≤ 2 ^ (42588 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 29641. -/
theorem theta29176_psi_29641_bounds :
    (29663926 : ℝ) / 1000 ≤ Chebyshev.psi 29641 ∧ Chebyshev.psi 29641 ≤ (29664620 : ℝ) / 1000 := by
  have hl : 2 ^ 42796 ≤ Nat.lcmUpto 29641 := by decide +kernel
  have hu : Nat.lcmUpto 29641 ≤ 2 ^ (42796 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 29791. -/
theorem theta29176_psi_29791_bounds :
    (29780375 : ℝ) / 1000 ≤ Chebyshev.psi 29791 ∧ Chebyshev.psi 29791 ≤ (29781069 : ℝ) / 1000 := by
  have hl : 2 ^ 42964 ≤ Nat.lcmUpto 29791 := by decide +kernel
  have hu : Nat.lcmUpto 29791 ≤ 2 ^ (42964 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 29803. -/
theorem theta29176_psi_29803_bounds :
    (29790772 : ℝ) / 1000 ≤ Chebyshev.psi 29803 ∧ Chebyshev.psi 29803 ≤ (29791466 : ℝ) / 1000 := by
  have hl : 2 ^ 42979 ≤ Nat.lcmUpto 29803 := by decide +kernel
  have hu : Nat.lcmUpto 29803 ≤ 2 ^ (42979 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 29929. -/
theorem theta29176_psi_29929_bounds :
    (29919698 : ℝ) / 1000 ≤ Chebyshev.psi 29929 ∧ Chebyshev.psi 29929 ≤ (29920392 : ℝ) / 1000 := by
  have hl : 2 ^ 43165 ≤ Nat.lcmUpto 29929 := by decide +kernel
  have hu : Nat.lcmUpto 29929 ≤ 2 ^ (43165 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 30047. -/
theorem theta29176_psi_30047_bounds :
    (30002182 : ℝ) / 1000 ≤ Chebyshev.psi 30047 ∧ Chebyshev.psi 30047 ≤ (30002876 : ℝ) / 1000 := by
  have hl : 2 ^ 43284 ≤ Nat.lcmUpto 30047 := by decide +kernel
  have hu : Nat.lcmUpto 30047 ≤ 2 ^ (43284 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 30059. -/
theorem theta29176_psi_30059_bounds :
    (30012579 : ℝ) / 1000 ≤ Chebyshev.psi 30059 ∧ Chebyshev.psi 30059 ≤ (30013273 : ℝ) / 1000 := by
  have hl : 2 ^ 43299 ≤ Nat.lcmUpto 30059 := by decide +kernel
  have hu : Nat.lcmUpto 30059 ≤ 2 ^ (43299 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 30139. -/
theorem theta29176_psi_30139_bounds :
    (30126255 : ℝ) / 1000 ≤ Chebyshev.psi 30139 ∧ Chebyshev.psi 30139 ≤ (30126950 : ℝ) / 1000 := by
  have hl : 2 ^ 43463 ≤ Nat.lcmUpto 30139 := by decide +kernel
  have hu : Nat.lcmUpto 30139 ≤ 2 ^ (43463 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 30259. -/
theorem theta29176_psi_30259_bounds :
    (30239238 : ℝ) / 1000 ≤ Chebyshev.psi 30259 ∧ Chebyshev.psi 30259 ≤ (30239933 : ℝ) / 1000 := by
  have hl : 2 ^ 43626 ≤ Nat.lcmUpto 30259 := by decide +kernel
  have hu : Nat.lcmUpto 30259 ≤ 2 ^ (43626 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 30367. -/
theorem theta29176_psi_30367_bounds :
    (30342517 : ℝ) / 1000 ≤ Chebyshev.psi 30367 ∧ Chebyshev.psi 30367 ≤ (30343211 : ℝ) / 1000 := by
  have hl : 2 ^ 43775 ≤ Nat.lcmUpto 30367 := by decide +kernel
  have hu : Nat.lcmUpto 30367 ≤ 2 ^ (43775 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 30469. -/
theorem theta29176_psi_30469_bounds :
    (30425002 : ℝ) / 1000 ≤ Chebyshev.psi 30469 ∧ Chebyshev.psi 30469 ≤ (30425696 : ℝ) / 1000 := by
  have hl : 2 ^ 43894 ≤ Nat.lcmUpto 30469 := by decide +kernel
  have hu : Nat.lcmUpto 30469 ≤ 2 ^ (43894 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 30559. -/
theorem theta29176_psi_30559_bounds :
    (30528281 : ℝ) / 1000 ≤ Chebyshev.psi 30559 ∧ Chebyshev.psi 30559 ≤ (30528975 : ℝ) / 1000 := by
  have hl : 2 ^ 44043 ≤ Nat.lcmUpto 30559 := by decide +kernel
  have hu : Nat.lcmUpto 30559 ≤ 2 ^ (44043 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 30661. -/
theorem theta29176_psi_30661_bounds :
    (30601061 : ℝ) / 1000 ≤ Chebyshev.psi 30661 ∧ Chebyshev.psi 30661 ≤ (30601755 : ℝ) / 1000 := by
  have hl : 2 ^ 44148 ≤ Nat.lcmUpto 30661 := by decide +kernel
  have hu : Nat.lcmUpto 30661 ≤ 2 ^ (44148 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- Every batch cell has a checked theta lower bound. -/
theorem theta29176_lower : ∀ r ∈ theta29176Cells, (r.lo : ℝ) / 1000 ≤ Chebyshev.theta r.a := by
  intro r hr
  simp only [theta29176Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change (28965207 : ℝ) / 1000 ≤ Chebyshev.theta (↑(29176 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 29176) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 29173) (b := 29176) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta29176_psi_29173_bounds.1]
  · change (29119779 : ℝ) / 1000 ≤ Chebyshev.theta (↑(29330 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 29330) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 29327) (b := 29330) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta29176_psi_29327_bounds.1]
  · change (29294452 : ℝ) / 1000 ≤ Chebyshev.theta (↑(29484 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 29484) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 29483) (b := 29484) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta29176_psi_29483_bounds.1]
  · change (29438626 : ℝ) / 1000 ≤ Chebyshev.theta (↑(29659 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 29659) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 29641) (b := 29659) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta29176_psi_29641_bounds.1]
  · change (29565472 : ℝ) / 1000 ≤ Chebyshev.theta (↑(29803 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 29803) (by norm_num only) (by norm_num only)
    linarith only [hd, theta29176_psi_29803_bounds.1]
  · change (29694398 : ℝ) / 1000 ≤ Chebyshev.theta (↑(29930 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 29930) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 29929) (b := 29930) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta29176_psi_29929_bounds.1]
  · change (29787279 : ℝ) / 1000 ≤ Chebyshev.theta (↑(30059 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 30059) (by norm_num only) (by norm_num only)
    linarith only [hd, theta29176_psi_30059_bounds.1]
  · change (29900955 : ℝ) / 1000 ≤ Chebyshev.theta (↑(30152 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 30152) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 30139) (b := 30152) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta29176_psi_30139_bounds.1]
  · change (30013938 : ℝ) / 1000 ≤ Chebyshev.theta (↑(30265 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 30265) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 30259) (b := 30265) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta29176_psi_30259_bounds.1]
  · change (30117217 : ℝ) / 1000 ≤ Chebyshev.theta (↑(30378 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 30378) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 30367) (b := 30378) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta29176_psi_30367_bounds.1]
  · change (30199702 : ℝ) / 1000 ≤ Chebyshev.theta (↑(30482 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 30482) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 30469) (b := 30482) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta29176_psi_30469_bounds.1]
  · change (30302981 : ℝ) / 1000 ≤ Chebyshev.theta (↑(30564 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 30564) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 30559) (b := 30564) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta29176_psi_30559_bounds.1]

/-- Every batch cell has a checked theta upper bound. -/
theorem theta29176_upper :
    ∀ r ∈ theta29176Cells, Chebyshev.theta (r.b - 1 : ℕ) ≤ (r.hi : ℝ) / 1000 := by
  intro r hr
  simp only [theta29176Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change Chebyshev.theta (↑(29329 : ℕ) : ℝ) ≤ (29345773 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 29329
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 29327) (b := 29329) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta29176_psi_29327_bounds.2]
  · change Chebyshev.theta (↑(29483 : ℕ) : ℝ) ≤ (29520446 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 29483
    linarith only [hd, theta29176_psi_29483_bounds.2]
  · change Chebyshev.theta (↑(29658 : ℕ) : ℝ) ≤ (29664620 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 29658
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 29641) (b := 29658) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta29176_psi_29641_bounds.2]
  · change Chebyshev.theta (↑(29802 : ℕ) : ℝ) ≤ (29781069 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 29802
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 29791) (b := 29802) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta29176_psi_29791_bounds.2]
  · change Chebyshev.theta (↑(29929 : ℕ) : ℝ) ≤ (29920392 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 29929
    linarith only [hd, theta29176_psi_29929_bounds.2]
  · change Chebyshev.theta (↑(30058 : ℕ) : ℝ) ≤ (30002876 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 30058
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 30047) (b := 30058) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta29176_psi_30047_bounds.2]
  · change Chebyshev.theta (↑(30151 : ℕ) : ℝ) ≤ (30126950 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 30151
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 30139) (b := 30151) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta29176_psi_30139_bounds.2]
  · change Chebyshev.theta (↑(30264 : ℕ) : ℝ) ≤ (30239933 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 30264
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 30259) (b := 30264) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta29176_psi_30259_bounds.2]
  · change Chebyshev.theta (↑(30377 : ℕ) : ℝ) ≤ (30343211 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 30377
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 30367) (b := 30377) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta29176_psi_30367_bounds.2]
  · change Chebyshev.theta (↑(30481 : ℕ) : ℝ) ≤ (30425696 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 30481
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 30469) (b := 30481) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta29176_psi_30469_bounds.2]
  · change Chebyshev.theta (↑(30563 : ℕ) : ℝ) ≤ (30528975 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 30563
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 30559) (b := 30563) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta29176_psi_30559_bounds.2]
  · change Chebyshev.theta (↑(30666 : ℕ) : ℝ) ≤ (30601755 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 30666
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 30661) (b := 30666) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta29176_psi_30661_bounds.2]

/-- The envelope bound applies at every cell a endpoint. -/
theorem theta29176_a :
    ∀ r ∈ theta29176Cells,
      (r.ca : ℝ) / 1000 ≤
        Real.sqrt r.a *
          (Real.log r.a * (Real.log r.a - Real.log (Real.log r.a)) / (8 * Real.pi)) := by
  intro r hr
  simp only [theta29176Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 29176 *
          (Real.log 29176 * (Real.log 29176 - Real.log (Real.log 29176)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 29330 *
          (Real.log 29330 * (Real.log 29330 - Real.log (Real.log 29330)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 29484 *
          (Real.log 29484 * (Real.log 29484 - Real.log (Real.log 29484)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 29659 *
          (Real.log 29659 * (Real.log 29659 - Real.log (Real.log 29659)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 29803 *
          (Real.log 29803 * (Real.log 29803 - Real.log (Real.log 29803)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 29930 *
          (Real.log 29930 * (Real.log 29930 - Real.log (Real.log 29930)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 30059 *
          (Real.log 30059 * (Real.log 30059 - Real.log (Real.log 30059)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 30152 *
          (Real.log 30152 * (Real.log 30152 - Real.log (Real.log 30152)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 30265 *
          (Real.log 30265 * (Real.log 30265 - Real.log (Real.log 30265)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 30378 *
          (Real.log 30378 * (Real.log 30378 - Real.log (Real.log 30378)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 30482 *
          (Real.log 30482 * (Real.log 30482 - Real.log (Real.log 30482)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 30564 *
          (Real.log 30564 * (Real.log 30564 - Real.log (Real.log 30564)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)

/-- The envelope bound applies at every cell b endpoint. -/
theorem theta29176_b :
    ∀ r ∈ theta29176Cells,
      (r.cb : ℝ) / 1000 ≤
        Real.sqrt r.b *
          (Real.log r.b * (Real.log r.b - Real.log (Real.log r.b)) / (8 * Real.pi)) := by
  intro r hr
  simp only [theta29176Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 29330 *
          (Real.log 29330 * (Real.log 29330 - Real.log (Real.log 29330)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 29484 *
          (Real.log 29484 * (Real.log 29484 - Real.log (Real.log 29484)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 29659 *
          (Real.log 29659 * (Real.log 29659 - Real.log (Real.log 29659)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 29803 *
          (Real.log 29803 * (Real.log 29803 - Real.log (Real.log 29803)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 29930 *
          (Real.log 29930 * (Real.log 29930 - Real.log (Real.log 29930)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 30059 *
          (Real.log 30059 * (Real.log 30059 - Real.log (Real.log 30059)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 30152 *
          (Real.log 30152 * (Real.log 30152 - Real.log (Real.log 30152)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 30265 *
          (Real.log 30265 * (Real.log 30265 - Real.log (Real.log 30265)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 30378 *
          (Real.log 30378 * (Real.log 30378 - Real.log (Real.log 30378)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 30482 *
          (Real.log 30482 * (Real.log 30482 - Real.log (Real.log 30482)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 30564 *
          (Real.log 30564 * (Real.log 30564 - Real.log (Real.log 30564)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 30667 *
          (Real.log 30667 * (Real.log 30667 - Real.log (Real.log 30667)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)

/-- The cells form a checked chain covering `[29176, 30667)`. -/
theorem theta29176_check : leeNosalChainCheck 29176 30667 theta29176Cells = true := by
  decide +kernel

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
