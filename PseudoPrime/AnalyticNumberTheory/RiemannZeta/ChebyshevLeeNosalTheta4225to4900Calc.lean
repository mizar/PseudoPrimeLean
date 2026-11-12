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
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSmallDefect4900
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalLogCheck
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalMonotone
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalChecker

/-! # Batch certificate for Lee–Nosal theta cells -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The local cells store endpoint bounds in thousandths. -/
def theta4225Cells : List LeeNosalCell :=
  [⟨4225, 4268, 4135302, 4282264, 133000, 133000⟩, ⟨4268, 4327, 4194220, 4323853, 133000, 133000⟩,
    ⟨4327, 4377, 4244126, 4382770, 133000, 133000⟩, ⟨4377, 4427, 4294726, 4424359, 133000, 133000⟩,
    ⟨4427, 4469, 4336315, 4466641, 133000, 133000⟩, ⟨4469, 4511, 4378597, 4504071, 133000, 133000⟩,
    ⟨4511, 4549, 4416027, 4546353, 133000, 133000⟩, ⟨4549, 4599, 4466626, 4596953, 133000, 133000⟩,
    ⟨4599, 4641, 4508908, 4630917, 133000, 133000⟩, ⟨4641, 4675, 4542873, 4681517, 133000, 133000⟩,
    ⟨4675, 4726, 4593472, 4723799, 133000, 133000⟩, ⟨4726, 4768, 4635754, 4757763, 133000, 133000⟩,
    ⟨4768, 4802, 4669719, 4808362, 133000, 133000⟩, ⟨4802, 4853, 4720318, 4834009, 133000, 133000⟩,
    ⟨4853, 4878, 4745965, 4859655, 133000, 133000⟩, ⟨4878, 4900, 4771611, 4867973, 133000, 133000⟩]

/-- The kernel-checked prefix bounds for 4219. -/
theorem theta4225_psi_4219_bounds :
    (4222652 : ℝ) / 1000 ≤ Chebyshev.psi 4219 ∧ Chebyshev.psi 4219 ≤ (4223346 : ℝ) / 1000 := by
  have hl : 2 ^ 6092 ≤ Nat.lcmUpto 4219 := by decide +kernel
  have hu : Nat.lcmUpto 4219 ≤ 2 ^ (6092 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 4261. -/
theorem theta4225_psi_4261_bounds :
    (4281570 : ℝ) / 1000 ≤ Chebyshev.psi 4261 ∧ Chebyshev.psi 4261 ≤ (4282264 : ℝ) / 1000 := by
  have hl : 2 ^ 6177 ≤ Nat.lcmUpto 4261 := by decide +kernel
  have hu : Nat.lcmUpto 4261 ≤ 2 ^ (6177 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 4297. -/
theorem theta4225_psi_4297_bounds :
    (4323158 : ℝ) / 1000 ≤ Chebyshev.psi 4297 ∧ Chebyshev.psi 4297 ≤ (4323853 : ℝ) / 1000 := by
  have hl : 2 ^ 6237 ≤ Nat.lcmUpto 4297 := by decide +kernel
  have hu : Nat.lcmUpto 4297 ≤ 2 ^ (6237 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 4327. -/
theorem theta4225_psi_4327_bounds :
    (4331476 : ℝ) / 1000 ≤ Chebyshev.psi 4327 ∧ Chebyshev.psi 4327 ≤ (4332170 : ℝ) / 1000 := by
  have hl : 2 ^ 6249 ≤ Nat.lcmUpto 4327 := by decide +kernel
  have hu : Nat.lcmUpto 4327 ≤ 2 ^ (6249 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 4373. -/
theorem theta4225_psi_4373_bounds :
    (4382076 : ℝ) / 1000 ≤ Chebyshev.psi 4373 ∧ Chebyshev.psi 4373 ≤ (4382770 : ℝ) / 1000 := by
  have hl : 2 ^ 6322 ≤ Nat.lcmUpto 4373 := by decide +kernel
  have hu : Nat.lcmUpto 4373 ≤ 2 ^ (6322 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 4423. -/
theorem theta4225_psi_4423_bounds :
    (4423665 : ℝ) / 1000 ≤ Chebyshev.psi 4423 ∧ Chebyshev.psi 4423 ≤ (4424359 : ℝ) / 1000 := by
  have hl : 2 ^ 6382 ≤ Nat.lcmUpto 4423 := by decide +kernel
  have hu : Nat.lcmUpto 4423 ≤ 2 ^ (6382 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 4463. -/
theorem theta4225_psi_4463_bounds :
    (4465947 : ℝ) / 1000 ≤ Chebyshev.psi 4463 ∧ Chebyshev.psi 4463 ≤ (4466641 : ℝ) / 1000 := by
  have hl : 2 ^ 6443 ≤ Nat.lcmUpto 4463 := by decide +kernel
  have hu : Nat.lcmUpto 4463 ≤ 2 ^ (6443 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 4507. -/
theorem theta4225_psi_4507_bounds :
    (4503377 : ℝ) / 1000 ≤ Chebyshev.psi 4507 ∧ Chebyshev.psi 4507 ≤ (4504071 : ℝ) / 1000 := by
  have hl : 2 ^ 6497 ≤ Nat.lcmUpto 4507 := by decide +kernel
  have hu : Nat.lcmUpto 4507 ≤ 2 ^ (6497 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 4547. -/
theorem theta4225_psi_4547_bounds :
    (4545659 : ℝ) / 1000 ≤ Chebyshev.psi 4547 ∧ Chebyshev.psi 4547 ≤ (4546353 : ℝ) / 1000 := by
  have hl : 2 ^ 6558 ≤ Nat.lcmUpto 4547 := by decide +kernel
  have hu : Nat.lcmUpto 4547 ≤ 2 ^ (6558 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 4549. -/
theorem theta4225_psi_4549_bounds :
    (4553976 : ℝ) / 1000 ≤ Chebyshev.psi 4549 ∧ Chebyshev.psi 4549 ≤ (4554671 : ℝ) / 1000 := by
  have hl : 2 ^ 6570 ≤ Nat.lcmUpto 4549 := by decide +kernel
  have hu : Nat.lcmUpto 4549 ≤ 2 ^ (6570 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 4597. -/
theorem theta4225_psi_4597_bounds :
    (4596258 : ℝ) / 1000 ≤ Chebyshev.psi 4597 ∧ Chebyshev.psi 4597 ≤ (4596953 : ℝ) / 1000 := by
  have hl : 2 ^ 6631 ≤ Nat.lcmUpto 4597 := by decide +kernel
  have hu : Nat.lcmUpto 4597 ≤ 2 ^ (6631 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 4639. -/
theorem theta4225_psi_4639_bounds :
    (4630223 : ℝ) / 1000 ≤ Chebyshev.psi 4639 ∧ Chebyshev.psi 4639 ≤ (4630917 : ℝ) / 1000 := by
  have hl : 2 ^ 6680 ≤ Nat.lcmUpto 4639 := by decide +kernel
  have hu : Nat.lcmUpto 4639 ≤ 2 ^ (6680 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 4673. -/
theorem theta4225_psi_4673_bounds :
    (4680822 : ℝ) / 1000 ≤ Chebyshev.psi 4673 ∧ Chebyshev.psi 4673 ≤ (4681517 : ℝ) / 1000 := by
  have hl : 2 ^ 6753 ≤ Nat.lcmUpto 4673 := by decide +kernel
  have hu : Nat.lcmUpto 4673 ≤ 2 ^ (6753 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 4723. -/
theorem theta4225_psi_4723_bounds :
    (4723104 : ℝ) / 1000 ≤ Chebyshev.psi 4723 ∧ Chebyshev.psi 4723 ≤ (4723799 : ℝ) / 1000 := by
  have hl : 2 ^ 6814 ≤ Nat.lcmUpto 4723 := by decide +kernel
  have hu : Nat.lcmUpto 4723 ≤ 2 ^ (6814 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 4759. -/
theorem theta4225_psi_4759_bounds :
    (4757069 : ℝ) / 1000 ≤ Chebyshev.psi 4759 ∧ Chebyshev.psi 4759 ≤ (4757763 : ℝ) / 1000 := by
  have hl : 2 ^ 6863 ≤ Nat.lcmUpto 4759 := by decide +kernel
  have hu : Nat.lcmUpto 4759 ≤ 2 ^ (6863 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 4801. -/
theorem theta4225_psi_4801_bounds :
    (4807668 : ℝ) / 1000 ≤ Chebyshev.psi 4801 ∧ Chebyshev.psi 4801 ≤ (4808362 : ℝ) / 1000 := by
  have hl : 2 ^ 6936 ≤ Nat.lcmUpto 4801 := by decide +kernel
  have hu : Nat.lcmUpto 4801 ≤ 2 ^ (6936 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 4831. -/
theorem theta4225_psi_4831_bounds :
    (4833315 : ℝ) / 1000 ≤ Chebyshev.psi 4831 ∧ Chebyshev.psi 4831 ≤ (4834009 : ℝ) / 1000 := by
  have hl : 2 ^ 6973 ≤ Nat.lcmUpto 4831 := by decide +kernel
  have hu : Nat.lcmUpto 4831 ≤ 2 ^ (6973 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 4877. -/
theorem theta4225_psi_4877_bounds :
    (4858961 : ℝ) / 1000 ≤ Chebyshev.psi 4877 ∧ Chebyshev.psi 4877 ≤ (4859655 : ℝ) / 1000 := by
  have hl : 2 ^ 7010 ≤ Nat.lcmUpto 4877 := by decide +kernel
  have hu : Nat.lcmUpto 4877 ≤ 2 ^ (7010 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 4889. -/
theorem theta4225_psi_4889_bounds :
    (4867279 : ℝ) / 1000 ≤ Chebyshev.psi 4889 ∧ Chebyshev.psi 4889 ≤ (4867973 : ℝ) / 1000 := by
  have hl : 2 ^ 7022 ≤ Nat.lcmUpto 4889 := by decide +kernel
  have hu : Nat.lcmUpto 4889 ≤ 2 ^ (7022 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- A rational certificate bounds the envelope from 4225 onward. -/
theorem theta4225_envelope {t : ℝ} (ht : 4225 ≤ t) :
    (133 : ℝ) ≤
      Real.sqrt t * (Real.log t * (Real.log t - Real.log (Real.log t)) / (8 * Real.pi)) := by
  have h :=
    lee_nosal_envelope_of_log_checks (N := 4225) (lo := 834 / 100) (hi := 835 / 100) (vlo :=
      212 / 100) (vhi := 213 / 100) (c := 133) (j := 13) (k := 4) (n := 32) (m := 32)
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by decide +kernel) (by decide +kernel) (by norm_num only)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact
    h.trans
      (lee_nosal_envelope_mono (x := 4225) (y := t)
        (Real.exp_one_lt_three.le.trans (by norm_num only)) ht)

/-- Every batch cell has a checked theta lower bound. -/
theorem theta4225_lower : ∀ r ∈ theta4225Cells, (r.lo : ℝ) / 1000 ≤ Chebyshev.theta r.a := by
  intro r hr
  simp only [theta4225Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · change (4135302 : ℝ) / 1000 ≤ Chebyshev.theta (↑(4225 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_8735 (x := 4225) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 4219) (b := 4225) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta4225_psi_4219_bounds.1]
  · change (4194220 : ℝ) / 1000 ≤ Chebyshev.theta (↑(4268 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_8735 (x := 4268) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 4261) (b := 4268) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta4225_psi_4261_bounds.1]
  · change (4244126 : ℝ) / 1000 ≤ Chebyshev.theta (↑(4327 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_8735 (x := 4327) (by norm_num only) (by norm_num only)
    linarith only [hd, theta4225_psi_4327_bounds.1]
  · change (4294726 : ℝ) / 1000 ≤ Chebyshev.theta (↑(4377 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_8735 (x := 4377) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 4373) (b := 4377) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta4225_psi_4373_bounds.1]
  · change (4336315 : ℝ) / 1000 ≤ Chebyshev.theta (↑(4427 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_8735 (x := 4427) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 4423) (b := 4427) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta4225_psi_4423_bounds.1]
  · change (4378597 : ℝ) / 1000 ≤ Chebyshev.theta (↑(4469 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_8735 (x := 4469) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 4463) (b := 4469) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta4225_psi_4463_bounds.1]
  · change (4416027 : ℝ) / 1000 ≤ Chebyshev.theta (↑(4511 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_8735 (x := 4511) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 4507) (b := 4511) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta4225_psi_4507_bounds.1]
  · change (4466626 : ℝ) / 1000 ≤ Chebyshev.theta (↑(4549 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_8735 (x := 4549) (by norm_num only) (by norm_num only)
    linarith only [hd, theta4225_psi_4549_bounds.1]
  · change (4508908 : ℝ) / 1000 ≤ Chebyshev.theta (↑(4599 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_8735 (x := 4599) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 4597) (b := 4599) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta4225_psi_4597_bounds.1]
  · change (4542873 : ℝ) / 1000 ≤ Chebyshev.theta (↑(4641 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_8735 (x := 4641) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 4639) (b := 4641) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta4225_psi_4639_bounds.1]
  · change (4593472 : ℝ) / 1000 ≤ Chebyshev.theta (↑(4675 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_8735 (x := 4675) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 4673) (b := 4675) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta4225_psi_4673_bounds.1]
  · change (4635754 : ℝ) / 1000 ≤ Chebyshev.theta (↑(4726 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_8735 (x := 4726) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 4723) (b := 4726) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta4225_psi_4723_bounds.1]
  · change (4669719 : ℝ) / 1000 ≤ Chebyshev.theta (↑(4768 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_8735 (x := 4768) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 4759) (b := 4768) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta4225_psi_4759_bounds.1]
  · change (4720318 : ℝ) / 1000 ≤ Chebyshev.theta (↑(4802 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_8735 (x := 4802) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 4801) (b := 4802) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta4225_psi_4801_bounds.1]
  · change (4745965 : ℝ) / 1000 ≤ Chebyshev.theta (↑(4853 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_8735 (x := 4853) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 4831) (b := 4853) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta4225_psi_4831_bounds.1]
  · change (4771611 : ℝ) / 1000 ≤ Chebyshev.theta (↑(4878 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_8735 (x := 4878) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 4877) (b := 4878) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta4225_psi_4877_bounds.1]

/-- Every batch cell has a checked theta upper bound. -/
theorem theta4225_upper :
    ∀ r ∈ theta4225Cells, Chebyshev.theta (r.b - 1 : ℕ) ≤ (r.hi : ℝ) / 1000 := by
  intro r hr
  simp only [theta4225Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · change Chebyshev.theta (↑(4267 : ℕ) : ℝ) ≤ (4282264 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 4267
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 4261) (b := 4267) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta4225_psi_4261_bounds.2]
  · change Chebyshev.theta (↑(4326 : ℕ) : ℝ) ≤ (4323853 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 4326
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 4297) (b := 4326) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta4225_psi_4297_bounds.2]
  · change Chebyshev.theta (↑(4376 : ℕ) : ℝ) ≤ (4382770 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 4376
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 4373) (b := 4376) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta4225_psi_4373_bounds.2]
  · change Chebyshev.theta (↑(4426 : ℕ) : ℝ) ≤ (4424359 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 4426
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 4423) (b := 4426) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta4225_psi_4423_bounds.2]
  · change Chebyshev.theta (↑(4468 : ℕ) : ℝ) ≤ (4466641 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 4468
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 4463) (b := 4468) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta4225_psi_4463_bounds.2]
  · change Chebyshev.theta (↑(4510 : ℕ) : ℝ) ≤ (4504071 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 4510
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 4507) (b := 4510) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta4225_psi_4507_bounds.2]
  · change Chebyshev.theta (↑(4548 : ℕ) : ℝ) ≤ (4546353 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 4548
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 4547) (b := 4548) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta4225_psi_4547_bounds.2]
  · change Chebyshev.theta (↑(4598 : ℕ) : ℝ) ≤ (4596953 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 4598
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 4597) (b := 4598) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta4225_psi_4597_bounds.2]
  · change Chebyshev.theta (↑(4640 : ℕ) : ℝ) ≤ (4630917 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 4640
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 4639) (b := 4640) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta4225_psi_4639_bounds.2]
  · change Chebyshev.theta (↑(4674 : ℕ) : ℝ) ≤ (4681517 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 4674
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 4673) (b := 4674) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta4225_psi_4673_bounds.2]
  · change Chebyshev.theta (↑(4725 : ℕ) : ℝ) ≤ (4723799 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 4725
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 4723) (b := 4725) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta4225_psi_4723_bounds.2]
  · change Chebyshev.theta (↑(4767 : ℕ) : ℝ) ≤ (4757763 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 4767
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 4759) (b := 4767) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta4225_psi_4759_bounds.2]
  · change Chebyshev.theta (↑(4801 : ℕ) : ℝ) ≤ (4808362 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 4801
    linarith only [hd, theta4225_psi_4801_bounds.2]
  · change Chebyshev.theta (↑(4852 : ℕ) : ℝ) ≤ (4834009 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 4852
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 4831) (b := 4852) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta4225_psi_4831_bounds.2]
  · change Chebyshev.theta (↑(4877 : ℕ) : ℝ) ≤ (4859655 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 4877
    linarith only [hd, theta4225_psi_4877_bounds.2]
  · change Chebyshev.theta (↑(4899 : ℕ) : ℝ) ≤ (4867973 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 4899
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 4889) (b := 4899) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta4225_psi_4889_bounds.2]

/-- The envelope bound applies at every cell a endpoint. -/
theorem theta4225_a :
    ∀ r ∈ theta4225Cells,
      (r.ca : ℝ) / 1000 ≤
        Real.sqrt r.a *
          (Real.log r.a * (Real.log r.a - Real.log (Real.log r.a)) / (8 * Real.pi)) := by
  intro r hr
  simp only [theta4225Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · change
      (133000 : ℝ) / 1000 ≤
        Real.sqrt 4225 *
          (Real.log 4225 * (Real.log 4225 - Real.log (Real.log 4225)) / (8 * Real.pi))
    norm_num only
    exact theta4225_envelope (by norm_num only)
  · change
      (133000 : ℝ) / 1000 ≤
        Real.sqrt 4268 *
          (Real.log 4268 * (Real.log 4268 - Real.log (Real.log 4268)) / (8 * Real.pi))
    norm_num only
    exact theta4225_envelope (by norm_num only)
  · change
      (133000 : ℝ) / 1000 ≤
        Real.sqrt 4327 *
          (Real.log 4327 * (Real.log 4327 - Real.log (Real.log 4327)) / (8 * Real.pi))
    norm_num only
    exact theta4225_envelope (by norm_num only)
  · change
      (133000 : ℝ) / 1000 ≤
        Real.sqrt 4377 *
          (Real.log 4377 * (Real.log 4377 - Real.log (Real.log 4377)) / (8 * Real.pi))
    norm_num only
    exact theta4225_envelope (by norm_num only)
  · change
      (133000 : ℝ) / 1000 ≤
        Real.sqrt 4427 *
          (Real.log 4427 * (Real.log 4427 - Real.log (Real.log 4427)) / (8 * Real.pi))
    norm_num only
    exact theta4225_envelope (by norm_num only)
  · change
      (133000 : ℝ) / 1000 ≤
        Real.sqrt 4469 *
          (Real.log 4469 * (Real.log 4469 - Real.log (Real.log 4469)) / (8 * Real.pi))
    norm_num only
    exact theta4225_envelope (by norm_num only)
  · change
      (133000 : ℝ) / 1000 ≤
        Real.sqrt 4511 *
          (Real.log 4511 * (Real.log 4511 - Real.log (Real.log 4511)) / (8 * Real.pi))
    norm_num only
    exact theta4225_envelope (by norm_num only)
  · change
      (133000 : ℝ) / 1000 ≤
        Real.sqrt 4549 *
          (Real.log 4549 * (Real.log 4549 - Real.log (Real.log 4549)) / (8 * Real.pi))
    norm_num only
    exact theta4225_envelope (by norm_num only)
  · change
      (133000 : ℝ) / 1000 ≤
        Real.sqrt 4599 *
          (Real.log 4599 * (Real.log 4599 - Real.log (Real.log 4599)) / (8 * Real.pi))
    norm_num only
    exact theta4225_envelope (by norm_num only)
  · change
      (133000 : ℝ) / 1000 ≤
        Real.sqrt 4641 *
          (Real.log 4641 * (Real.log 4641 - Real.log (Real.log 4641)) / (8 * Real.pi))
    norm_num only
    exact theta4225_envelope (by norm_num only)
  · change
      (133000 : ℝ) / 1000 ≤
        Real.sqrt 4675 *
          (Real.log 4675 * (Real.log 4675 - Real.log (Real.log 4675)) / (8 * Real.pi))
    norm_num only
    exact theta4225_envelope (by norm_num only)
  · change
      (133000 : ℝ) / 1000 ≤
        Real.sqrt 4726 *
          (Real.log 4726 * (Real.log 4726 - Real.log (Real.log 4726)) / (8 * Real.pi))
    norm_num only
    exact theta4225_envelope (by norm_num only)
  · change
      (133000 : ℝ) / 1000 ≤
        Real.sqrt 4768 *
          (Real.log 4768 * (Real.log 4768 - Real.log (Real.log 4768)) / (8 * Real.pi))
    norm_num only
    exact theta4225_envelope (by norm_num only)
  · change
      (133000 : ℝ) / 1000 ≤
        Real.sqrt 4802 *
          (Real.log 4802 * (Real.log 4802 - Real.log (Real.log 4802)) / (8 * Real.pi))
    norm_num only
    exact theta4225_envelope (by norm_num only)
  · change
      (133000 : ℝ) / 1000 ≤
        Real.sqrt 4853 *
          (Real.log 4853 * (Real.log 4853 - Real.log (Real.log 4853)) / (8 * Real.pi))
    norm_num only
    exact theta4225_envelope (by norm_num only)
  · change
      (133000 : ℝ) / 1000 ≤
        Real.sqrt 4878 *
          (Real.log 4878 * (Real.log 4878 - Real.log (Real.log 4878)) / (8 * Real.pi))
    norm_num only
    exact theta4225_envelope (by norm_num only)

/-- The envelope bound applies at every cell b endpoint. -/
theorem theta4225_b :
    ∀ r ∈ theta4225Cells,
      (r.cb : ℝ) / 1000 ≤
        Real.sqrt r.b *
          (Real.log r.b * (Real.log r.b - Real.log (Real.log r.b)) / (8 * Real.pi)) := by
  intro r hr
  simp only [theta4225Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · change
      (133000 : ℝ) / 1000 ≤
        Real.sqrt 4268 *
          (Real.log 4268 * (Real.log 4268 - Real.log (Real.log 4268)) / (8 * Real.pi))
    norm_num only
    exact theta4225_envelope (by norm_num only)
  · change
      (133000 : ℝ) / 1000 ≤
        Real.sqrt 4327 *
          (Real.log 4327 * (Real.log 4327 - Real.log (Real.log 4327)) / (8 * Real.pi))
    norm_num only
    exact theta4225_envelope (by norm_num only)
  · change
      (133000 : ℝ) / 1000 ≤
        Real.sqrt 4377 *
          (Real.log 4377 * (Real.log 4377 - Real.log (Real.log 4377)) / (8 * Real.pi))
    norm_num only
    exact theta4225_envelope (by norm_num only)
  · change
      (133000 : ℝ) / 1000 ≤
        Real.sqrt 4427 *
          (Real.log 4427 * (Real.log 4427 - Real.log (Real.log 4427)) / (8 * Real.pi))
    norm_num only
    exact theta4225_envelope (by norm_num only)
  · change
      (133000 : ℝ) / 1000 ≤
        Real.sqrt 4469 *
          (Real.log 4469 * (Real.log 4469 - Real.log (Real.log 4469)) / (8 * Real.pi))
    norm_num only
    exact theta4225_envelope (by norm_num only)
  · change
      (133000 : ℝ) / 1000 ≤
        Real.sqrt 4511 *
          (Real.log 4511 * (Real.log 4511 - Real.log (Real.log 4511)) / (8 * Real.pi))
    norm_num only
    exact theta4225_envelope (by norm_num only)
  · change
      (133000 : ℝ) / 1000 ≤
        Real.sqrt 4549 *
          (Real.log 4549 * (Real.log 4549 - Real.log (Real.log 4549)) / (8 * Real.pi))
    norm_num only
    exact theta4225_envelope (by norm_num only)
  · change
      (133000 : ℝ) / 1000 ≤
        Real.sqrt 4599 *
          (Real.log 4599 * (Real.log 4599 - Real.log (Real.log 4599)) / (8 * Real.pi))
    norm_num only
    exact theta4225_envelope (by norm_num only)
  · change
      (133000 : ℝ) / 1000 ≤
        Real.sqrt 4641 *
          (Real.log 4641 * (Real.log 4641 - Real.log (Real.log 4641)) / (8 * Real.pi))
    norm_num only
    exact theta4225_envelope (by norm_num only)
  · change
      (133000 : ℝ) / 1000 ≤
        Real.sqrt 4675 *
          (Real.log 4675 * (Real.log 4675 - Real.log (Real.log 4675)) / (8 * Real.pi))
    norm_num only
    exact theta4225_envelope (by norm_num only)
  · change
      (133000 : ℝ) / 1000 ≤
        Real.sqrt 4726 *
          (Real.log 4726 * (Real.log 4726 - Real.log (Real.log 4726)) / (8 * Real.pi))
    norm_num only
    exact theta4225_envelope (by norm_num only)
  · change
      (133000 : ℝ) / 1000 ≤
        Real.sqrt 4768 *
          (Real.log 4768 * (Real.log 4768 - Real.log (Real.log 4768)) / (8 * Real.pi))
    norm_num only
    exact theta4225_envelope (by norm_num only)
  · change
      (133000 : ℝ) / 1000 ≤
        Real.sqrt 4802 *
          (Real.log 4802 * (Real.log 4802 - Real.log (Real.log 4802)) / (8 * Real.pi))
    norm_num only
    exact theta4225_envelope (by norm_num only)
  · change
      (133000 : ℝ) / 1000 ≤
        Real.sqrt 4853 *
          (Real.log 4853 * (Real.log 4853 - Real.log (Real.log 4853)) / (8 * Real.pi))
    norm_num only
    exact theta4225_envelope (by norm_num only)
  · change
      (133000 : ℝ) / 1000 ≤
        Real.sqrt 4878 *
          (Real.log 4878 * (Real.log 4878 - Real.log (Real.log 4878)) / (8 * Real.pi))
    norm_num only
    exact theta4225_envelope (by norm_num only)
  · change
      (133000 : ℝ) / 1000 ≤
        Real.sqrt 4900 *
          (Real.log 4900 * (Real.log 4900 - Real.log (Real.log 4900)) / (8 * Real.pi))
    norm_num only
    exact theta4225_envelope (by norm_num only)

/-- The cells form a checked chain covering `[4225, 4900)`. -/
theorem theta4225_check : leeNosalChainCheck 4225 4900 theta4225Cells = true := by decide +kernel

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
