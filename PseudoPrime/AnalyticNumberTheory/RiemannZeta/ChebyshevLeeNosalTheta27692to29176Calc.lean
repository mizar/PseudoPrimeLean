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
def theta27692Cells : List LeeNosalCell :=
  [⟨27692, 27774, 27409091, 27748068, 365000, 365000⟩,
    ⟨27774, 27887, 27522074, 27870755, 365000, 365000⟩,
    ⟨27887, 28009, 27644761, 28008692, 365000, 365000⟩,
    ⟨28009, 28147, 27782698, 28141776, 365000, 365000⟩,
    ⟨28147, 28280, 27915782, 28244362, 365000, 365000⟩,
    ⟨28280, 28383, 28018368, 28326153, 365000, 365000⟩,
    ⟨28383, 28465, 28100159, 28428739, 365000, 365000⟩,
    ⟨28465, 28567, 28202745, 28534097, 365000, 365000⟩,
    ⟨28567, 28673, 28308103, 28708770, 365000, 365000⟩,
    ⟨28673, 28847, 28482776, 28882750, 365000, 365000⟩,
    ⟨28847, 29021, 28656756, 29026925, 365000, 365000⟩,
    ⟨29021, 29176, 28811328, 29191201, 365000, 365000⟩]

/-- The kernel-checked prefix bounds for 27691. -/
theorem theta27692_psi_27691_bounds :
    (27634391 : ℝ) / 1000 ≤ Chebyshev.psi 27691 ∧ Chebyshev.psi 27691 ≤ (27635085 : ℝ) / 1000 := by
  have hl : 2 ^ 39868 ≤ Nat.lcmUpto 27691 := by decide +kernel
  have hu : Nat.lcmUpto 27691 ≤ 2 ^ (39868 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 27773. -/
theorem theta27692_psi_27773_bounds :
    (27747374 : ℝ) / 1000 ≤ Chebyshev.psi 27773 ∧ Chebyshev.psi 27773 ≤ (27748068 : ℝ) / 1000 := by
  have hl : 2 ^ 40031 ≤ Nat.lcmUpto 27773 := by decide +kernel
  have hu : Nat.lcmUpto 27773 ≤ 2 ^ (40031 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 27883. -/
theorem theta27692_psi_27883_bounds :
    (27870061 : ℝ) / 1000 ≤ Chebyshev.psi 27883 ∧ Chebyshev.psi 27883 ≤ (27870755 : ℝ) / 1000 := by
  have hl : 2 ^ 40208 ≤ Nat.lcmUpto 27883 := by decide +kernel
  have hu : Nat.lcmUpto 27883 ≤ 2 ^ (40208 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 28001. -/
theorem theta27692_psi_28001_bounds :
    (28007998 : ℝ) / 1000 ≤ Chebyshev.psi 28001 ∧ Chebyshev.psi 28001 ≤ (28008692 : ℝ) / 1000 := by
  have hl : 2 ^ 40407 ≤ Nat.lcmUpto 28001 := by decide +kernel
  have hu : Nat.lcmUpto 28001 ≤ 2 ^ (40407 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 28123. -/
theorem theta27692_psi_28123_bounds :
    (28141082 : ℝ) / 1000 ≤ Chebyshev.psi 28123 ∧ Chebyshev.psi 28123 ≤ (28141776 : ℝ) / 1000 := by
  have hl : 2 ^ 40599 ≤ Nat.lcmUpto 28123 := by decide +kernel
  have hu : Nat.lcmUpto 28123 ≤ 2 ^ (40599 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 28279. -/
theorem theta27692_psi_28279_bounds :
    (28243668 : ℝ) / 1000 ≤ Chebyshev.psi 28279 ∧ Chebyshev.psi 28279 ≤ (28244362 : ℝ) / 1000 := by
  have hl : 2 ^ 40747 ≤ Nat.lcmUpto 28279 := by decide +kernel
  have hu : Nat.lcmUpto 28279 ≤ 2 ^ (40747 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 28351. -/
theorem theta27692_psi_28351_bounds :
    (28325459 : ℝ) / 1000 ≤ Chebyshev.psi 28351 ∧ Chebyshev.psi 28351 ≤ (28326153 : ℝ) / 1000 := by
  have hl : 2 ^ 40865 ≤ Nat.lcmUpto 28351 := by decide +kernel
  have hu : Nat.lcmUpto 28351 ≤ 2 ^ (40865 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 28463. -/
theorem theta27692_psi_28463_bounds :
    (28428045 : ℝ) / 1000 ≤ Chebyshev.psi 28463 ∧ Chebyshev.psi 28463 ≤ (28428739 : ℝ) / 1000 := by
  have hl : 2 ^ 41013 ≤ Nat.lcmUpto 28463 := by decide +kernel
  have hu : Nat.lcmUpto 28463 ≤ 2 ^ (41013 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 28561. -/
theorem theta27692_psi_28561_bounds :
    (28533403 : ℝ) / 1000 ≤ Chebyshev.psi 28561 ∧ Chebyshev.psi 28561 ≤ (28534097 : ℝ) / 1000 := by
  have hl : 2 ^ 41165 ≤ Nat.lcmUpto 28561 := by decide +kernel
  have hu : Nat.lcmUpto 28561 ≤ 2 ^ (41165 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 28669. -/
theorem theta27692_psi_28669_bounds :
    (28708076 : ℝ) / 1000 ≤ Chebyshev.psi 28669 ∧ Chebyshev.psi 28669 ≤ (28708770 : ℝ) / 1000 := by
  have hl : 2 ^ 41417 ≤ Nat.lcmUpto 28669 := by decide +kernel
  have hu : Nat.lcmUpto 28669 ≤ 2 ^ (41417 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 28843. -/
theorem theta27692_psi_28843_bounds :
    (28882056 : ℝ) / 1000 ≤ Chebyshev.psi 28843 ∧ Chebyshev.psi 28843 ≤ (28882750 : ℝ) / 1000 := by
  have hl : 2 ^ 41668 ≤ Nat.lcmUpto 28843 := by decide +kernel
  have hu : Nat.lcmUpto 28843 ≤ 2 ^ (41668 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 29017. -/
theorem theta27692_psi_29017_bounds :
    (29026231 : ℝ) / 1000 ≤ Chebyshev.psi 29017 ∧ Chebyshev.psi 29017 ≤ (29026925 : ℝ) / 1000 := by
  have hl : 2 ^ 41876 ≤ Nat.lcmUpto 29017 := by decide +kernel
  have hu : Nat.lcmUpto 29017 ≤ 2 ^ (41876 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 29021. -/
theorem theta27692_psi_29021_bounds :
    (29036628 : ℝ) / 1000 ≤ Chebyshev.psi 29021 ∧ Chebyshev.psi 29021 ≤ (29037322 : ℝ) / 1000 := by
  have hl : 2 ^ 41891 ≤ Nat.lcmUpto 29021 := by decide +kernel
  have hu : Nat.lcmUpto 29021 ≤ 2 ^ (41891 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 29173. -/
theorem theta27692_psi_29173_bounds :
    (29190507 : ℝ) / 1000 ≤ Chebyshev.psi 29173 ∧ Chebyshev.psi 29173 ≤ (29191201 : ℝ) / 1000 := by
  have hl : 2 ^ 42113 ≤ Nat.lcmUpto 29173 := by decide +kernel
  have hu : Nat.lcmUpto 29173 ≤ 2 ^ (42113 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- Every batch cell has a checked theta lower bound. -/
theorem theta27692_lower : ∀ r ∈ theta27692Cells, (r.lo : ℝ) / 1000 ≤ Chebyshev.theta r.a := by
  intro r hr
  simp only [theta27692Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change (27409091 : ℝ) / 1000 ≤ Chebyshev.theta (↑(27692 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 27692) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 27691) (b := 27692) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta27692_psi_27691_bounds.1]
  · change (27522074 : ℝ) / 1000 ≤ Chebyshev.theta (↑(27774 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 27774) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 27773) (b := 27774) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta27692_psi_27773_bounds.1]
  · change (27644761 : ℝ) / 1000 ≤ Chebyshev.theta (↑(27887 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 27887) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 27883) (b := 27887) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta27692_psi_27883_bounds.1]
  · change (27782698 : ℝ) / 1000 ≤ Chebyshev.theta (↑(28009 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 28009) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 28001) (b := 28009) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta27692_psi_28001_bounds.1]
  · change (27915782 : ℝ) / 1000 ≤ Chebyshev.theta (↑(28147 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 28147) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 28123) (b := 28147) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta27692_psi_28123_bounds.1]
  · change (28018368 : ℝ) / 1000 ≤ Chebyshev.theta (↑(28280 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 28280) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 28279) (b := 28280) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta27692_psi_28279_bounds.1]
  · change (28100159 : ℝ) / 1000 ≤ Chebyshev.theta (↑(28383 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 28383) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 28351) (b := 28383) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta27692_psi_28351_bounds.1]
  · change (28202745 : ℝ) / 1000 ≤ Chebyshev.theta (↑(28465 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 28465) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 28463) (b := 28465) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta27692_psi_28463_bounds.1]
  · change (28308103 : ℝ) / 1000 ≤ Chebyshev.theta (↑(28567 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 28567) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 28561) (b := 28567) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta27692_psi_28561_bounds.1]
  · change (28482776 : ℝ) / 1000 ≤ Chebyshev.theta (↑(28673 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 28673) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 28669) (b := 28673) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta27692_psi_28669_bounds.1]
  · change (28656756 : ℝ) / 1000 ≤ Chebyshev.theta (↑(28847 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 28847) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 28843) (b := 28847) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta27692_psi_28843_bounds.1]
  · change (28811328 : ℝ) / 1000 ≤ Chebyshev.theta (↑(29021 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 29021) (by norm_num only) (by norm_num only)
    linarith only [hd, theta27692_psi_29021_bounds.1]

/-- Every batch cell has a checked theta upper bound. -/
theorem theta27692_upper :
    ∀ r ∈ theta27692Cells, Chebyshev.theta (r.b - 1 : ℕ) ≤ (r.hi : ℝ) / 1000 := by
  intro r hr
  simp only [theta27692Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change Chebyshev.theta (↑(27773 : ℕ) : ℝ) ≤ (27748068 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 27773
    linarith only [hd, theta27692_psi_27773_bounds.2]
  · change Chebyshev.theta (↑(27886 : ℕ) : ℝ) ≤ (27870755 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 27886
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 27883) (b := 27886) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta27692_psi_27883_bounds.2]
  · change Chebyshev.theta (↑(28008 : ℕ) : ℝ) ≤ (28008692 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 28008
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 28001) (b := 28008) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta27692_psi_28001_bounds.2]
  · change Chebyshev.theta (↑(28146 : ℕ) : ℝ) ≤ (28141776 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 28146
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 28123) (b := 28146) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta27692_psi_28123_bounds.2]
  · change Chebyshev.theta (↑(28279 : ℕ) : ℝ) ≤ (28244362 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 28279
    linarith only [hd, theta27692_psi_28279_bounds.2]
  · change Chebyshev.theta (↑(28382 : ℕ) : ℝ) ≤ (28326153 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 28382
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 28351) (b := 28382) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta27692_psi_28351_bounds.2]
  · change Chebyshev.theta (↑(28464 : ℕ) : ℝ) ≤ (28428739 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 28464
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 28463) (b := 28464) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta27692_psi_28463_bounds.2]
  · change Chebyshev.theta (↑(28566 : ℕ) : ℝ) ≤ (28534097 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 28566
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 28561) (b := 28566) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta27692_psi_28561_bounds.2]
  · change Chebyshev.theta (↑(28672 : ℕ) : ℝ) ≤ (28708770 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 28672
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 28669) (b := 28672) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta27692_psi_28669_bounds.2]
  · change Chebyshev.theta (↑(28846 : ℕ) : ℝ) ≤ (28882750 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 28846
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 28843) (b := 28846) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta27692_psi_28843_bounds.2]
  · change Chebyshev.theta (↑(29020 : ℕ) : ℝ) ≤ (29026925 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 29020
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 29017) (b := 29020) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta27692_psi_29017_bounds.2]
  · change Chebyshev.theta (↑(29175 : ℕ) : ℝ) ≤ (29191201 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 29175
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 29173) (b := 29175) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta27692_psi_29173_bounds.2]

/-- The envelope bound applies at every cell a endpoint. -/
theorem theta27692_a :
    ∀ r ∈ theta27692Cells,
      (r.ca : ℝ) / 1000 ≤
        Real.sqrt r.a *
          (Real.log r.a * (Real.log r.a - Real.log (Real.log r.a)) / (8 * Real.pi)) := by
  intro r hr
  simp only [theta27692Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 27692 *
          (Real.log 27692 * (Real.log 27692 - Real.log (Real.log 27692)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 27774 *
          (Real.log 27774 * (Real.log 27774 - Real.log (Real.log 27774)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 27887 *
          (Real.log 27887 * (Real.log 27887 - Real.log (Real.log 27887)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 28009 *
          (Real.log 28009 * (Real.log 28009 - Real.log (Real.log 28009)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 28147 *
          (Real.log 28147 * (Real.log 28147 - Real.log (Real.log 28147)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 28280 *
          (Real.log 28280 * (Real.log 28280 - Real.log (Real.log 28280)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 28383 *
          (Real.log 28383 * (Real.log 28383 - Real.log (Real.log 28383)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 28465 *
          (Real.log 28465 * (Real.log 28465 - Real.log (Real.log 28465)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 28567 *
          (Real.log 28567 * (Real.log 28567 - Real.log (Real.log 28567)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 28673 *
          (Real.log 28673 * (Real.log 28673 - Real.log (Real.log 28673)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 28847 *
          (Real.log 28847 * (Real.log 28847 - Real.log (Real.log 28847)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 29021 *
          (Real.log 29021 * (Real.log 29021 - Real.log (Real.log 29021)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)

/-- The envelope bound applies at every cell b endpoint. -/
theorem theta27692_b :
    ∀ r ∈ theta27692Cells,
      (r.cb : ℝ) / 1000 ≤
        Real.sqrt r.b *
          (Real.log r.b * (Real.log r.b - Real.log (Real.log r.b)) / (8 * Real.pi)) := by
  intro r hr
  simp only [theta27692Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 27774 *
          (Real.log 27774 * (Real.log 27774 - Real.log (Real.log 27774)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 27887 *
          (Real.log 27887 * (Real.log 27887 - Real.log (Real.log 27887)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 28009 *
          (Real.log 28009 * (Real.log 28009 - Real.log (Real.log 28009)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 28147 *
          (Real.log 28147 * (Real.log 28147 - Real.log (Real.log 28147)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 28280 *
          (Real.log 28280 * (Real.log 28280 - Real.log (Real.log 28280)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 28383 *
          (Real.log 28383 * (Real.log 28383 - Real.log (Real.log 28383)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 28465 *
          (Real.log 28465 * (Real.log 28465 - Real.log (Real.log 28465)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 28567 *
          (Real.log 28567 * (Real.log 28567 - Real.log (Real.log 28567)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 28673 *
          (Real.log 28673 * (Real.log 28673 - Real.log (Real.log 28673)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 28847 *
          (Real.log 28847 * (Real.log 28847 - Real.log (Real.log 28847)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 29021 *
          (Real.log 29021 * (Real.log 29021 - Real.log (Real.log 29021)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 29176 *
          (Real.log 29176 * (Real.log 29176 - Real.log (Real.log 29176)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)

/-- The cells form a checked chain covering `[27692, 29176)`. -/
theorem theta27692_check : leeNosalChainCheck 27692 29176 theta27692Cells = true := by
  decide +kernel

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
