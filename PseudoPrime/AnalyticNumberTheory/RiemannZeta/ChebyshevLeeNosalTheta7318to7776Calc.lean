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
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSmallDefect7776
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalEnvelope5625
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalMonotone
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalChecker

/-! # Batch certificate for Lee–Nosal theta cells -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The local cells store endpoint bounds in thousandths. -/
def theta7318Cells : List LeeNosalCell :=
  [⟨7318, 7363, 7198329, 7357065, 165000, 165000⟩, ⟨7363, 7407, 7242691, 7375087, 165000, 165000⟩,
    ⟨7407, 7425, 7260712, 7392415, 165000, 165000⟩, ⟨7425, 7443, 7278041, 7401426, 165000, 165000⟩,
    ⟨7443, 7452, 7287052, 7410437, 165000, 165000⟩, ⟨7452, 7461, 7296063, 7428459, 165000, 165000⟩,
    ⟨7461, 7479, 7314085, 7437470, 165000, 165000⟩, ⟨7479, 7488, 7323096, 7454798, 165000, 165000⟩,
    ⟨7488, 7505, 7340424, 7472820, 165000, 165000⟩, ⟨7505, 7523, 7358446, 7490842, 165000, 165000⟩,
    ⟨7523, 7550, 7385479, 7544214, 165000, 165000⟩, ⟨7550, 7594, 7429840, 7606598, 165000, 165000⟩,
    ⟨7594, 7657, 7492224, 7660663, 165000, 165000⟩, ⟨7657, 7711, 7546289, 7723046, 165000, 165000⟩,
    ⟨7711, 7773, 7608672, 7785430, 165000, 165000⟩, ⟨7773, 7776, 7671055, 7785430, 165000, 165000⟩]

/-- The kernel-checked prefix bounds for 7309. -/
theorem theta7318_psi_7309_bounds :
    (7312009 : ℝ) / 1000 ≤ Chebyshev.psi 7309 ∧ Chebyshev.psi 7309 ≤ (7312703 : ℝ) / 1000 := by
  have hl : 2 ^ 10549 ≤ Nat.lcmUpto 7309 := by decide +kernel
  have hu : Nat.lcmUpto 7309 ≤ 2 ^ (10549 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 7351. -/
theorem theta7318_psi_7351_bounds :
    (7356371 : ℝ) / 1000 ≤ Chebyshev.psi 7351 ∧ Chebyshev.psi 7351 ≤ (7357065 : ℝ) / 1000 := by
  have hl : 2 ^ 10613 ≤ Nat.lcmUpto 7351 := by decide +kernel
  have hu : Nat.lcmUpto 7351 ≤ 2 ^ (10613 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 7393. -/
theorem theta7318_psi_7393_bounds :
    (7374392 : ℝ) / 1000 ≤ Chebyshev.psi 7393 ∧ Chebyshev.psi 7393 ≤ (7375087 : ℝ) / 1000 := by
  have hl : 2 ^ 10639 ≤ Nat.lcmUpto 7393 := by decide +kernel
  have hu : Nat.lcmUpto 7393 ≤ 2 ^ (10639 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 7417. -/
theorem theta7318_psi_7417_bounds :
    (7391721 : ℝ) / 1000 ≤ Chebyshev.psi 7417 ∧ Chebyshev.psi 7417 ≤ (7392415 : ℝ) / 1000 := by
  have hl : 2 ^ 10664 ≤ Nat.lcmUpto 7417 := by decide +kernel
  have hu : Nat.lcmUpto 7417 ≤ 2 ^ (10664 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 7433. -/
theorem theta7318_psi_7433_bounds :
    (7400732 : ℝ) / 1000 ≤ Chebyshev.psi 7433 ∧ Chebyshev.psi 7433 ≤ (7401426 : ℝ) / 1000 := by
  have hl : 2 ^ 10677 ≤ Nat.lcmUpto 7433 := by decide +kernel
  have hu : Nat.lcmUpto 7433 ≤ 2 ^ (10677 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 7451. -/
theorem theta7318_psi_7451_bounds :
    (7409743 : ℝ) / 1000 ≤ Chebyshev.psi 7451 ∧ Chebyshev.psi 7451 ≤ (7410437 : ℝ) / 1000 := by
  have hl : 2 ^ 10690 ≤ Nat.lcmUpto 7451 := by decide +kernel
  have hu : Nat.lcmUpto 7451 ≤ 2 ^ (10690 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 7459. -/
theorem theta7318_psi_7459_bounds :
    (7427765 : ℝ) / 1000 ≤ Chebyshev.psi 7459 ∧ Chebyshev.psi 7459 ≤ (7428459 : ℝ) / 1000 := by
  have hl : 2 ^ 10716 ≤ Nat.lcmUpto 7459 := by decide +kernel
  have hu : Nat.lcmUpto 7459 ≤ 2 ^ (10716 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 7477. -/
theorem theta7318_psi_7477_bounds :
    (7436776 : ℝ) / 1000 ≤ Chebyshev.psi 7477 ∧ Chebyshev.psi 7477 ≤ (7437470 : ℝ) / 1000 := by
  have hl : 2 ^ 10729 ≤ Nat.lcmUpto 7477 := by decide +kernel
  have hu : Nat.lcmUpto 7477 ≤ 2 ^ (10729 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 7487. -/
theorem theta7318_psi_7487_bounds :
    (7454104 : ℝ) / 1000 ≤ Chebyshev.psi 7487 ∧ Chebyshev.psi 7487 ≤ (7454798 : ℝ) / 1000 := by
  have hl : 2 ^ 10754 ≤ Nat.lcmUpto 7487 := by decide +kernel
  have hu : Nat.lcmUpto 7487 ≤ 2 ^ (10754 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 7499. -/
theorem theta7318_psi_7499_bounds :
    (7472126 : ℝ) / 1000 ≤ Chebyshev.psi 7499 ∧ Chebyshev.psi 7499 ≤ (7472820 : ℝ) / 1000 := by
  have hl : 2 ^ 10780 ≤ Nat.lcmUpto 7499 := by decide +kernel
  have hu : Nat.lcmUpto 7499 ≤ 2 ^ (10780 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 7517. -/
theorem theta7318_psi_7517_bounds :
    (7490148 : ℝ) / 1000 ≤ Chebyshev.psi 7517 ∧ Chebyshev.psi 7517 ≤ (7490842 : ℝ) / 1000 := by
  have hl : 2 ^ 10806 ≤ Nat.lcmUpto 7517 := by decide +kernel
  have hu : Nat.lcmUpto 7517 ≤ 2 ^ (10806 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 7523. -/
theorem theta7318_psi_7523_bounds :
    (7499159 : ℝ) / 1000 ≤ Chebyshev.psi 7523 ∧ Chebyshev.psi 7523 ≤ (7499853 : ℝ) / 1000 := by
  have hl : 2 ^ 10819 ≤ Nat.lcmUpto 7523 := by decide +kernel
  have hu : Nat.lcmUpto 7523 ≤ 2 ^ (10819 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 7549. -/
theorem theta7318_psi_7549_bounds :
    (7543520 : ℝ) / 1000 ≤ Chebyshev.psi 7549 ∧ Chebyshev.psi 7549 ≤ (7544214 : ℝ) / 1000 := by
  have hl : 2 ^ 10883 ≤ Nat.lcmUpto 7549 := by decide +kernel
  have hu : Nat.lcmUpto 7549 ≤ 2 ^ (10883 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 7591. -/
theorem theta7318_psi_7591_bounds :
    (7605904 : ℝ) / 1000 ≤ Chebyshev.psi 7591 ∧ Chebyshev.psi 7591 ≤ (7606598 : ℝ) / 1000 := by
  have hl : 2 ^ 10973 ≤ Nat.lcmUpto 7591 := by decide +kernel
  have hu : Nat.lcmUpto 7591 ≤ 2 ^ (10973 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 7649. -/
theorem theta7318_psi_7649_bounds :
    (7659969 : ℝ) / 1000 ≤ Chebyshev.psi 7649 ∧ Chebyshev.psi 7649 ≤ (7660663 : ℝ) / 1000 := by
  have hl : 2 ^ 11051 ≤ Nat.lcmUpto 7649 := by decide +kernel
  have hu : Nat.lcmUpto 7649 ≤ 2 ^ (11051 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 7703. -/
theorem theta7318_psi_7703_bounds :
    (7722352 : ℝ) / 1000 ≤ Chebyshev.psi 7703 ∧ Chebyshev.psi 7703 ≤ (7723046 : ℝ) / 1000 := by
  have hl : 2 ^ 11141 ≤ Nat.lcmUpto 7703 := by decide +kernel
  have hu : Nat.lcmUpto 7703 ≤ 2 ^ (11141 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 7759. -/
theorem theta7318_psi_7759_bounds :
    (7784735 : ℝ) / 1000 ≤ Chebyshev.psi 7759 ∧ Chebyshev.psi 7759 ≤ (7785430 : ℝ) / 1000 := by
  have hl : 2 ^ 11231 ≤ Nat.lcmUpto 7759 := by decide +kernel
  have hu : Nat.lcmUpto 7759 ≤ 2 ^ (11231 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- Every batch cell has a checked theta lower bound. -/
theorem theta7318_lower : ∀ r ∈ theta7318Cells, (r.lo : ℝ) / 1000 ≤ Chebyshev.theta r.a := by
  intro r hr
  simp only [theta7318Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · change (7198329 : ℝ) / 1000 ≤ Chebyshev.theta (↑(7318 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_11368 (x := 7318) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 7309) (b := 7318) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta7318_psi_7309_bounds.1]
  · change (7242691 : ℝ) / 1000 ≤ Chebyshev.theta (↑(7363 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_11368 (x := 7363) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 7351) (b := 7363) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta7318_psi_7351_bounds.1]
  · change (7260712 : ℝ) / 1000 ≤ Chebyshev.theta (↑(7407 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_11368 (x := 7407) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 7393) (b := 7407) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta7318_psi_7393_bounds.1]
  · change (7278041 : ℝ) / 1000 ≤ Chebyshev.theta (↑(7425 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_11368 (x := 7425) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 7417) (b := 7425) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta7318_psi_7417_bounds.1]
  · change (7287052 : ℝ) / 1000 ≤ Chebyshev.theta (↑(7443 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_11368 (x := 7443) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 7433) (b := 7443) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta7318_psi_7433_bounds.1]
  · change (7296063 : ℝ) / 1000 ≤ Chebyshev.theta (↑(7452 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_11368 (x := 7452) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 7451) (b := 7452) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta7318_psi_7451_bounds.1]
  · change (7314085 : ℝ) / 1000 ≤ Chebyshev.theta (↑(7461 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_11368 (x := 7461) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 7459) (b := 7461) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta7318_psi_7459_bounds.1]
  · change (7323096 : ℝ) / 1000 ≤ Chebyshev.theta (↑(7479 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_11368 (x := 7479) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 7477) (b := 7479) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta7318_psi_7477_bounds.1]
  · change (7340424 : ℝ) / 1000 ≤ Chebyshev.theta (↑(7488 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_11368 (x := 7488) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 7487) (b := 7488) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta7318_psi_7487_bounds.1]
  · change (7358446 : ℝ) / 1000 ≤ Chebyshev.theta (↑(7505 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_11368 (x := 7505) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 7499) (b := 7505) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta7318_psi_7499_bounds.1]
  · change (7385479 : ℝ) / 1000 ≤ Chebyshev.theta (↑(7523 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_11368 (x := 7523) (by norm_num only) (by norm_num only)
    linarith only [hd, theta7318_psi_7523_bounds.1]
  · change (7429840 : ℝ) / 1000 ≤ Chebyshev.theta (↑(7550 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_11368 (x := 7550) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 7549) (b := 7550) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta7318_psi_7549_bounds.1]
  · change (7492224 : ℝ) / 1000 ≤ Chebyshev.theta (↑(7594 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_11368 (x := 7594) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 7591) (b := 7594) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta7318_psi_7591_bounds.1]
  · change (7546289 : ℝ) / 1000 ≤ Chebyshev.theta (↑(7657 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_11368 (x := 7657) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 7649) (b := 7657) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta7318_psi_7649_bounds.1]
  · change (7608672 : ℝ) / 1000 ≤ Chebyshev.theta (↑(7711 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_11368 (x := 7711) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 7703) (b := 7711) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta7318_psi_7703_bounds.1]
  · change (7671055 : ℝ) / 1000 ≤ Chebyshev.theta (↑(7773 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_11368 (x := 7773) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 7759) (b := 7773) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta7318_psi_7759_bounds.1]

/-- Every batch cell has a checked theta upper bound. -/
theorem theta7318_upper :
    ∀ r ∈ theta7318Cells, Chebyshev.theta (r.b - 1 : ℕ) ≤ (r.hi : ℝ) / 1000 := by
  intro r hr
  simp only [theta7318Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · change Chebyshev.theta (↑(7362 : ℕ) : ℝ) ≤ (7357065 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 7362
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 7351) (b := 7362) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta7318_psi_7351_bounds.2]
  · change Chebyshev.theta (↑(7406 : ℕ) : ℝ) ≤ (7375087 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 7406
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 7393) (b := 7406) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta7318_psi_7393_bounds.2]
  · change Chebyshev.theta (↑(7424 : ℕ) : ℝ) ≤ (7392415 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 7424
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 7417) (b := 7424) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta7318_psi_7417_bounds.2]
  · change Chebyshev.theta (↑(7442 : ℕ) : ℝ) ≤ (7401426 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 7442
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 7433) (b := 7442) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta7318_psi_7433_bounds.2]
  · change Chebyshev.theta (↑(7451 : ℕ) : ℝ) ≤ (7410437 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 7451
    linarith only [hd, theta7318_psi_7451_bounds.2]
  · change Chebyshev.theta (↑(7460 : ℕ) : ℝ) ≤ (7428459 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 7460
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 7459) (b := 7460) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta7318_psi_7459_bounds.2]
  · change Chebyshev.theta (↑(7478 : ℕ) : ℝ) ≤ (7437470 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 7478
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 7477) (b := 7478) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta7318_psi_7477_bounds.2]
  · change Chebyshev.theta (↑(7487 : ℕ) : ℝ) ≤ (7454798 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 7487
    linarith only [hd, theta7318_psi_7487_bounds.2]
  · change Chebyshev.theta (↑(7504 : ℕ) : ℝ) ≤ (7472820 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 7504
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 7499) (b := 7504) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta7318_psi_7499_bounds.2]
  · change Chebyshev.theta (↑(7522 : ℕ) : ℝ) ≤ (7490842 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 7522
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 7517) (b := 7522) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta7318_psi_7517_bounds.2]
  · change Chebyshev.theta (↑(7549 : ℕ) : ℝ) ≤ (7544214 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 7549
    linarith only [hd, theta7318_psi_7549_bounds.2]
  · change Chebyshev.theta (↑(7593 : ℕ) : ℝ) ≤ (7606598 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 7593
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 7591) (b := 7593) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta7318_psi_7591_bounds.2]
  · change Chebyshev.theta (↑(7656 : ℕ) : ℝ) ≤ (7660663 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 7656
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 7649) (b := 7656) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta7318_psi_7649_bounds.2]
  · change Chebyshev.theta (↑(7710 : ℕ) : ℝ) ≤ (7723046 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 7710
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 7703) (b := 7710) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta7318_psi_7703_bounds.2]
  · change Chebyshev.theta (↑(7772 : ℕ) : ℝ) ≤ (7785430 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 7772
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 7759) (b := 7772) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta7318_psi_7759_bounds.2]
  · change Chebyshev.theta (↑(7775 : ℕ) : ℝ) ≤ (7785430 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 7775
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 7759) (b := 7775) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta7318_psi_7759_bounds.2]

/-- The envelope bound applies at every cell a endpoint. -/
theorem theta7318_a :
    ∀ r ∈ theta7318Cells,
      (r.ca : ℝ) / 1000 ≤
        Real.sqrt r.a *
          (Real.log r.a * (Real.log r.a - Real.log (Real.log r.a)) / (8 * Real.pi)) := by
  intro r hr
  simp only [theta7318Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 7318 *
          (Real.log 7318 * (Real.log 7318 - Real.log (Real.log 7318)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 7363 *
          (Real.log 7363 * (Real.log 7363 - Real.log (Real.log 7363)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 7407 *
          (Real.log 7407 * (Real.log 7407 - Real.log (Real.log 7407)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 7425 *
          (Real.log 7425 * (Real.log 7425 - Real.log (Real.log 7425)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 7443 *
          (Real.log 7443 * (Real.log 7443 - Real.log (Real.log 7443)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 7452 *
          (Real.log 7452 * (Real.log 7452 - Real.log (Real.log 7452)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 7461 *
          (Real.log 7461 * (Real.log 7461 - Real.log (Real.log 7461)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 7479 *
          (Real.log 7479 * (Real.log 7479 - Real.log (Real.log 7479)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 7488 *
          (Real.log 7488 * (Real.log 7488 - Real.log (Real.log 7488)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 7505 *
          (Real.log 7505 * (Real.log 7505 - Real.log (Real.log 7505)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 7523 *
          (Real.log 7523 * (Real.log 7523 - Real.log (Real.log 7523)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 7550 *
          (Real.log 7550 * (Real.log 7550 - Real.log (Real.log 7550)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 7594 *
          (Real.log 7594 * (Real.log 7594 - Real.log (Real.log 7594)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 7657 *
          (Real.log 7657 * (Real.log 7657 - Real.log (Real.log 7657)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 7711 *
          (Real.log 7711 * (Real.log 7711 - Real.log (Real.log 7711)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 7773 *
          (Real.log 7773 * (Real.log 7773 - Real.log (Real.log 7773)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)

/-- The envelope bound applies at every cell b endpoint. -/
theorem theta7318_b :
    ∀ r ∈ theta7318Cells,
      (r.cb : ℝ) / 1000 ≤
        Real.sqrt r.b *
          (Real.log r.b * (Real.log r.b - Real.log (Real.log r.b)) / (8 * Real.pi)) := by
  intro r hr
  simp only [theta7318Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 7363 *
          (Real.log 7363 * (Real.log 7363 - Real.log (Real.log 7363)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 7407 *
          (Real.log 7407 * (Real.log 7407 - Real.log (Real.log 7407)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 7425 *
          (Real.log 7425 * (Real.log 7425 - Real.log (Real.log 7425)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 7443 *
          (Real.log 7443 * (Real.log 7443 - Real.log (Real.log 7443)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 7452 *
          (Real.log 7452 * (Real.log 7452 - Real.log (Real.log 7452)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 7461 *
          (Real.log 7461 * (Real.log 7461 - Real.log (Real.log 7461)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 7479 *
          (Real.log 7479 * (Real.log 7479 - Real.log (Real.log 7479)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 7488 *
          (Real.log 7488 * (Real.log 7488 - Real.log (Real.log 7488)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 7505 *
          (Real.log 7505 * (Real.log 7505 - Real.log (Real.log 7505)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 7523 *
          (Real.log 7523 * (Real.log 7523 - Real.log (Real.log 7523)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 7550 *
          (Real.log 7550 * (Real.log 7550 - Real.log (Real.log 7550)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 7594 *
          (Real.log 7594 * (Real.log 7594 - Real.log (Real.log 7594)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 7657 *
          (Real.log 7657 * (Real.log 7657 - Real.log (Real.log 7657)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 7711 *
          (Real.log 7711 * (Real.log 7711 - Real.log (Real.log 7711)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 7773 *
          (Real.log 7773 * (Real.log 7773 - Real.log (Real.log 7773)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 7776 *
          (Real.log 7776 * (Real.log 7776 - Real.log (Real.log 7776)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)

/-- The cells form a checked chain covering `[7318, 7776)`. -/
theorem theta7318_check : leeNosalChainCheck 7318 7776 theta7318Cells = true := by decide +kernel

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
