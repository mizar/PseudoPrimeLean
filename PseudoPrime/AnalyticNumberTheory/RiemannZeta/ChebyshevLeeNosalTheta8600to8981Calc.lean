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
def theta8600Cells : List LeeNosalCell :=
  [⟨8600, 8618, 8407159, 8574924, 211000, 211000⟩, ⟨8618, 8627, 8416170, 8583935, 211000, 211000⟩,
    ⟨8627, 8645, 8434192, 8610968, 211000, 211000⟩, ⟨8645, 8663, 8452214, 8619979, 211000, 211000⟩,
    ⟨8663, 8681, 8470236, 8647705, 211000, 211000⟩, ⟨8681, 8708, 8497961, 8692759, 211000, 211000⟩,
    ⟨8708, 8745, 8534005, 8737814, 211000, 211000⟩, ⟨8745, 8790, 8579060, 8783562, 211000, 211000⟩,
    ⟨8790, 8835, 8624807, 8828616, 211000, 211000⟩, ⟨8835, 8880, 8669862, 8883375, 211000, 211000⟩,
    ⟨8880, 8935, 8724621, 8929122, 211000, 211000⟩, ⟨8935, 8981, 8770368, 8974177, 211000, 211000⟩]

/-- The kernel-checked prefix bounds for 8599. -/
theorem theta8600_psi_8599_bounds :
    (8565219 : ℝ) / 1000 ≤ Chebyshev.psi 8599 ∧ Chebyshev.psi 8599 ≤ (8565913 : ℝ) / 1000 := by
  have hl : 2 ^ 12357 ≤ Nat.lcmUpto 8599 := by decide +kernel
  have hu : Nat.lcmUpto 8599 ≤ 2 ^ (12357 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 8609. -/
theorem theta8600_psi_8609_bounds :
    (8574230 : ℝ) / 1000 ≤ Chebyshev.psi 8609 ∧ Chebyshev.psi 8609 ≤ (8574924 : ℝ) / 1000 := by
  have hl : 2 ^ 12370 ≤ Nat.lcmUpto 8609 := by decide +kernel
  have hu : Nat.lcmUpto 8609 ≤ 2 ^ (12370 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 8623. -/
theorem theta8600_psi_8623_bounds :
    (8583241 : ℝ) / 1000 ≤ Chebyshev.psi 8623 ∧ Chebyshev.psi 8623 ≤ (8583935 : ℝ) / 1000 := by
  have hl : 2 ^ 12383 ≤ Nat.lcmUpto 8623 := by decide +kernel
  have hu : Nat.lcmUpto 8623 ≤ 2 ^ (12383 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 8627. -/
theorem theta8600_psi_8627_bounds :
    (8592252 : ℝ) / 1000 ≤ Chebyshev.psi 8627 ∧ Chebyshev.psi 8627 ≤ (8592946 : ℝ) / 1000 := by
  have hl : 2 ^ 12396 ≤ Nat.lcmUpto 8627 := by decide +kernel
  have hu : Nat.lcmUpto 8627 ≤ 2 ^ (12396 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 8641. -/
theorem theta8600_psi_8641_bounds :
    (8610274 : ℝ) / 1000 ≤ Chebyshev.psi 8641 ∧ Chebyshev.psi 8641 ≤ (8610968 : ℝ) / 1000 := by
  have hl : 2 ^ 12422 ≤ Nat.lcmUpto 8641 := by decide +kernel
  have hu : Nat.lcmUpto 8641 ≤ 2 ^ (12422 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 8647. -/
theorem theta8600_psi_8647_bounds :
    (8619285 : ℝ) / 1000 ≤ Chebyshev.psi 8647 ∧ Chebyshev.psi 8647 ≤ (8619979 : ℝ) / 1000 := by
  have hl : 2 ^ 12435 ≤ Nat.lcmUpto 8647 := by decide +kernel
  have hu : Nat.lcmUpto 8647 ≤ 2 ^ (12435 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 8663. -/
theorem theta8600_psi_8663_bounds :
    (8628296 : ℝ) / 1000 ≤ Chebyshev.psi 8663 ∧ Chebyshev.psi 8663 ≤ (8628990 : ℝ) / 1000 := by
  have hl : 2 ^ 12448 ≤ Nat.lcmUpto 8663 := by decide +kernel
  have hu : Nat.lcmUpto 8663 ≤ 2 ^ (12448 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 8677. -/
theorem theta8600_psi_8677_bounds :
    (8647011 : ℝ) / 1000 ≤ Chebyshev.psi 8677 ∧ Chebyshev.psi 8677 ≤ (8647705 : ℝ) / 1000 := by
  have hl : 2 ^ 12475 ≤ Nat.lcmUpto 8677 := by decide +kernel
  have hu : Nat.lcmUpto 8677 ≤ 2 ^ (12475 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 8681. -/
theorem theta8600_psi_8681_bounds :
    (8656021 : ℝ) / 1000 ≤ Chebyshev.psi 8681 ∧ Chebyshev.psi 8681 ≤ (8656716 : ℝ) / 1000 := by
  have hl : 2 ^ 12488 ≤ Nat.lcmUpto 8681 := by decide +kernel
  have hu : Nat.lcmUpto 8681 ≤ 2 ^ (12488 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 8707. -/
theorem theta8600_psi_8707_bounds :
    (8692065 : ℝ) / 1000 ≤ Chebyshev.psi 8707 ∧ Chebyshev.psi 8707 ≤ (8692759 : ℝ) / 1000 := by
  have hl : 2 ^ 12540 ≤ Nat.lcmUpto 8707 := by decide +kernel
  have hu : Nat.lcmUpto 8707 ≤ 2 ^ (12540 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 8741. -/
theorem theta8600_psi_8741_bounds :
    (8737120 : ℝ) / 1000 ≤ Chebyshev.psi 8741 ∧ Chebyshev.psi 8741 ≤ (8737814 : ℝ) / 1000 := by
  have hl : 2 ^ 12605 ≤ Nat.lcmUpto 8741 := by decide +kernel
  have hu : Nat.lcmUpto 8741 ≤ 2 ^ (12605 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 8783. -/
theorem theta8600_psi_8783_bounds :
    (8782867 : ℝ) / 1000 ≤ Chebyshev.psi 8783 ∧ Chebyshev.psi 8783 ≤ (8783562 : ℝ) / 1000 := by
  have hl : 2 ^ 12671 ≤ Nat.lcmUpto 8783 := by decide +kernel
  have hu : Nat.lcmUpto 8783 ≤ 2 ^ (12671 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 8831. -/
theorem theta8600_psi_8831_bounds :
    (8827922 : ℝ) / 1000 ≤ Chebyshev.psi 8831 ∧ Chebyshev.psi 8831 ≤ (8828616 : ℝ) / 1000 := by
  have hl : 2 ^ 12736 ≤ Nat.lcmUpto 8831 := by decide +kernel
  have hu : Nat.lcmUpto 8831 ≤ 2 ^ (12736 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 8867. -/
theorem theta8600_psi_8867_bounds :
    (8882681 : ℝ) / 1000 ≤ Chebyshev.psi 8867 ∧ Chebyshev.psi 8867 ≤ (8883375 : ℝ) / 1000 := by
  have hl : 2 ^ 12815 ≤ Nat.lcmUpto 8867 := by decide +kernel
  have hu : Nat.lcmUpto 8867 ≤ 2 ^ (12815 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 8933. -/
theorem theta8600_psi_8933_bounds :
    (8928428 : ℝ) / 1000 ≤ Chebyshev.psi 8933 ∧ Chebyshev.psi 8933 ≤ (8929122 : ℝ) / 1000 := by
  have hl : 2 ^ 12881 ≤ Nat.lcmUpto 8933 := by decide +kernel
  have hu : Nat.lcmUpto 8933 ≤ 2 ^ (12881 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 8971. -/
theorem theta8600_psi_8971_bounds :
    (8973483 : ℝ) / 1000 ≤ Chebyshev.psi 8971 ∧ Chebyshev.psi 8971 ≤ (8974177 : ℝ) / 1000 := by
  have hl : 2 ^ 12946 ≤ Nat.lcmUpto 8971 := by decide +kernel
  have hu : Nat.lcmUpto 8971 ≤ 2 ^ (12946 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- Every batch cell has a checked theta lower bound. -/
theorem theta8600_lower : ∀ r ∈ theta8600Cells, (r.lo : ℝ) / 1000 ≤ Chebyshev.theta r.a := by
  intro r hr
  simp only [theta8600Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change (8407159 : ℝ) / 1000 ≤ Chebyshev.theta (↑(8600 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 8600) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 8599) (b := 8600) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta8600_psi_8599_bounds.1]
  · change (8416170 : ℝ) / 1000 ≤ Chebyshev.theta (↑(8618 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 8618) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 8609) (b := 8618) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta8600_psi_8609_bounds.1]
  · change (8434192 : ℝ) / 1000 ≤ Chebyshev.theta (↑(8627 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 8627) (by norm_num only) (by norm_num only)
    linarith only [hd, theta8600_psi_8627_bounds.1]
  · change (8452214 : ℝ) / 1000 ≤ Chebyshev.theta (↑(8645 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 8645) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 8641) (b := 8645) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta8600_psi_8641_bounds.1]
  · change (8470236 : ℝ) / 1000 ≤ Chebyshev.theta (↑(8663 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 8663) (by norm_num only) (by norm_num only)
    linarith only [hd, theta8600_psi_8663_bounds.1]
  · change (8497961 : ℝ) / 1000 ≤ Chebyshev.theta (↑(8681 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 8681) (by norm_num only) (by norm_num only)
    linarith only [hd, theta8600_psi_8681_bounds.1]
  · change (8534005 : ℝ) / 1000 ≤ Chebyshev.theta (↑(8708 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 8708) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 8707) (b := 8708) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta8600_psi_8707_bounds.1]
  · change (8579060 : ℝ) / 1000 ≤ Chebyshev.theta (↑(8745 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 8745) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 8741) (b := 8745) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta8600_psi_8741_bounds.1]
  · change (8624807 : ℝ) / 1000 ≤ Chebyshev.theta (↑(8790 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 8790) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 8783) (b := 8790) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta8600_psi_8783_bounds.1]
  · change (8669862 : ℝ) / 1000 ≤ Chebyshev.theta (↑(8835 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 8835) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 8831) (b := 8835) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta8600_psi_8831_bounds.1]
  · change (8724621 : ℝ) / 1000 ≤ Chebyshev.theta (↑(8880 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 8880) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 8867) (b := 8880) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta8600_psi_8867_bounds.1]
  · change (8770368 : ℝ) / 1000 ≤ Chebyshev.theta (↑(8935 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 8935) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 8933) (b := 8935) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta8600_psi_8933_bounds.1]

/-- Every batch cell has a checked theta upper bound. -/
theorem theta8600_upper :
    ∀ r ∈ theta8600Cells, Chebyshev.theta (r.b - 1 : ℕ) ≤ (r.hi : ℝ) / 1000 := by
  intro r hr
  simp only [theta8600Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change Chebyshev.theta (↑(8617 : ℕ) : ℝ) ≤ (8574924 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 8617
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 8609) (b := 8617) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta8600_psi_8609_bounds.2]
  · change Chebyshev.theta (↑(8626 : ℕ) : ℝ) ≤ (8583935 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 8626
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 8623) (b := 8626) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta8600_psi_8623_bounds.2]
  · change Chebyshev.theta (↑(8644 : ℕ) : ℝ) ≤ (8610968 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 8644
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 8641) (b := 8644) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta8600_psi_8641_bounds.2]
  · change Chebyshev.theta (↑(8662 : ℕ) : ℝ) ≤ (8619979 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 8662
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 8647) (b := 8662) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta8600_psi_8647_bounds.2]
  · change Chebyshev.theta (↑(8680 : ℕ) : ℝ) ≤ (8647705 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 8680
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 8677) (b := 8680) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta8600_psi_8677_bounds.2]
  · change Chebyshev.theta (↑(8707 : ℕ) : ℝ) ≤ (8692759 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 8707
    linarith only [hd, theta8600_psi_8707_bounds.2]
  · change Chebyshev.theta (↑(8744 : ℕ) : ℝ) ≤ (8737814 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 8744
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 8741) (b := 8744) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta8600_psi_8741_bounds.2]
  · change Chebyshev.theta (↑(8789 : ℕ) : ℝ) ≤ (8783562 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 8789
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 8783) (b := 8789) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta8600_psi_8783_bounds.2]
  · change Chebyshev.theta (↑(8834 : ℕ) : ℝ) ≤ (8828616 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 8834
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 8831) (b := 8834) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta8600_psi_8831_bounds.2]
  · change Chebyshev.theta (↑(8879 : ℕ) : ℝ) ≤ (8883375 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 8879
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 8867) (b := 8879) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta8600_psi_8867_bounds.2]
  · change Chebyshev.theta (↑(8934 : ℕ) : ℝ) ≤ (8929122 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 8934
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 8933) (b := 8934) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta8600_psi_8933_bounds.2]
  · change Chebyshev.theta (↑(8980 : ℕ) : ℝ) ≤ (8974177 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 8980
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 8971) (b := 8980) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta8600_psi_8971_bounds.2]

/-- The envelope bound applies at every cell a endpoint. -/
theorem theta8600_a :
    ∀ r ∈ theta8600Cells,
      (r.ca : ℝ) / 1000 ≤
        Real.sqrt r.a *
          (Real.log r.a * (Real.log r.a - Real.log (Real.log r.a)) / (8 * Real.pi)) := by
  intro r hr
  simp only [theta8600Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 8600 *
          (Real.log 8600 * (Real.log 8600 - Real.log (Real.log 8600)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 8618 *
          (Real.log 8618 * (Real.log 8618 - Real.log (Real.log 8618)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 8627 *
          (Real.log 8627 * (Real.log 8627 - Real.log (Real.log 8627)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 8645 *
          (Real.log 8645 * (Real.log 8645 - Real.log (Real.log 8645)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 8663 *
          (Real.log 8663 * (Real.log 8663 - Real.log (Real.log 8663)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 8681 *
          (Real.log 8681 * (Real.log 8681 - Real.log (Real.log 8681)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 8708 *
          (Real.log 8708 * (Real.log 8708 - Real.log (Real.log 8708)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 8745 *
          (Real.log 8745 * (Real.log 8745 - Real.log (Real.log 8745)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 8790 *
          (Real.log 8790 * (Real.log 8790 - Real.log (Real.log 8790)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 8835 *
          (Real.log 8835 * (Real.log 8835 - Real.log (Real.log 8835)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 8880 *
          (Real.log 8880 * (Real.log 8880 - Real.log (Real.log 8880)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 8935 *
          (Real.log 8935 * (Real.log 8935 - Real.log (Real.log 8935)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)

/-- The envelope bound applies at every cell b endpoint. -/
theorem theta8600_b :
    ∀ r ∈ theta8600Cells,
      (r.cb : ℝ) / 1000 ≤
        Real.sqrt r.b *
          (Real.log r.b * (Real.log r.b - Real.log (Real.log r.b)) / (8 * Real.pi)) := by
  intro r hr
  simp only [theta8600Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 8618 *
          (Real.log 8618 * (Real.log 8618 - Real.log (Real.log 8618)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 8627 *
          (Real.log 8627 * (Real.log 8627 - Real.log (Real.log 8627)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 8645 *
          (Real.log 8645 * (Real.log 8645 - Real.log (Real.log 8645)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 8663 *
          (Real.log 8663 * (Real.log 8663 - Real.log (Real.log 8663)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 8681 *
          (Real.log 8681 * (Real.log 8681 - Real.log (Real.log 8681)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 8708 *
          (Real.log 8708 * (Real.log 8708 - Real.log (Real.log 8708)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 8745 *
          (Real.log 8745 * (Real.log 8745 - Real.log (Real.log 8745)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 8790 *
          (Real.log 8790 * (Real.log 8790 - Real.log (Real.log 8790)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 8835 *
          (Real.log 8835 * (Real.log 8835 - Real.log (Real.log 8835)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 8880 *
          (Real.log 8880 * (Real.log 8880 - Real.log (Real.log 8880)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 8935 *
          (Real.log 8935 * (Real.log 8935 - Real.log (Real.log 8935)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 8981 *
          (Real.log 8981 * (Real.log 8981 - Real.log (Real.log 8981)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)

/-- The cells form a checked chain covering `[8600, 8981)`. -/
theorem theta8600_check : leeNosalChainCheck 8600 8981 theta8600Cells = true := by decide +kernel

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
