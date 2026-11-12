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
def theta6204Cells : List LeeNosalCell :=
  [⟨6204, 6248, 6083055, 6245950, 165000, 165000⟩, ⟨6248, 6296, 6131576, 6297936, 165000, 165000⟩,
    ⟨6296, 6348, 6183562, 6367944, 165000, 165000⟩, ⟨6348, 6418, 6253569, 6437952, 165000, 165000⟩,
    ⟨6418, 6488, 6323577, 6499642, 165000, 165000⟩, ⟨6488, 6550, 6385267, 6534992, 165000, 165000⟩,
    ⟨6550, 6585, 6420618, 6597375, 165000, 165000⟩, ⟨6585, 6648, 6483001, 6632726, 165000, 165000⟩,
    ⟨6648, 6683, 6518352, 6676394, 165000, 165000⟩, ⟨6683, 6727, 6562020, 6729766, 165000, 165000⟩,
    ⟨6727, 6780, 6615392, 6773435, 165000, 165000⟩, ⟨6780, 6824, 6659061, 6817796, 165000, 165000⟩]

/-- The kernel-checked prefix bounds for 6203. -/
theorem theta6204_psi_6203_bounds :
    (6196735 : ℝ) / 1000 ≤ Chebyshev.psi 6203 ∧ Chebyshev.psi 6203 ≤ (6197429 : ℝ) / 1000 := by
  have hl : 2 ^ 8940 ≤ Nat.lcmUpto 6203 := by decide +kernel
  have hu : Nat.lcmUpto 6203 ≤ 2 ^ (8940 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 6247. -/
theorem theta6204_psi_6247_bounds :
    (6245256 : ℝ) / 1000 ≤ Chebyshev.psi 6247 ∧ Chebyshev.psi 6247 ≤ (6245950 : ℝ) / 1000 := by
  have hl : 2 ^ 9010 ≤ Nat.lcmUpto 6247 := by decide +kernel
  have hu : Nat.lcmUpto 6247 ≤ 2 ^ (9010 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 6287. -/
theorem theta6204_psi_6287_bounds :
    (6297242 : ℝ) / 1000 ≤ Chebyshev.psi 6287 ∧ Chebyshev.psi 6287 ≤ (6297936 : ℝ) / 1000 := by
  have hl : 2 ^ 9085 ≤ Nat.lcmUpto 6287 := by decide +kernel
  have hu : Nat.lcmUpto 6287 ≤ 2 ^ (9085 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 6343. -/
theorem theta6204_psi_6343_bounds :
    (6367249 : ℝ) / 1000 ≤ Chebyshev.psi 6343 ∧ Chebyshev.psi 6343 ≤ (6367944 : ℝ) / 1000 := by
  have hl : 2 ^ 9186 ≤ Nat.lcmUpto 6343 := by decide +kernel
  have hu : Nat.lcmUpto 6343 ≤ 2 ^ (9186 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 6397. -/
theorem theta6204_psi_6397_bounds :
    (6437257 : ℝ) / 1000 ≤ Chebyshev.psi 6397 ∧ Chebyshev.psi 6397 ≤ (6437952 : ℝ) / 1000 := by
  have hl : 2 ^ 9287 ≤ Nat.lcmUpto 6397 := by decide +kernel
  have hu : Nat.lcmUpto 6397 ≤ 2 ^ (9287 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 6481. -/
theorem theta6204_psi_6481_bounds :
    (6498947 : ℝ) / 1000 ≤ Chebyshev.psi 6481 ∧ Chebyshev.psi 6481 ≤ (6499642 : ℝ) / 1000 := by
  have hl : 2 ^ 9376 ≤ Nat.lcmUpto 6481 := by decide +kernel
  have hu : Nat.lcmUpto 6481 ≤ 2 ^ (9376 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 6547. -/
theorem theta6204_psi_6547_bounds :
    (6534298 : ℝ) / 1000 ≤ Chebyshev.psi 6547 ∧ Chebyshev.psi 6547 ≤ (6534992 : ℝ) / 1000 := by
  have hl : 2 ^ 9427 ≤ Nat.lcmUpto 6547 := by decide +kernel
  have hu : Nat.lcmUpto 6547 ≤ 2 ^ (9427 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 6581. -/
theorem theta6204_psi_6581_bounds :
    (6596681 : ℝ) / 1000 ≤ Chebyshev.psi 6581 ∧ Chebyshev.psi 6581 ≤ (6597375 : ℝ) / 1000 := by
  have hl : 2 ^ 9517 ≤ Nat.lcmUpto 6581 := by decide +kernel
  have hu : Nat.lcmUpto 6581 ≤ 2 ^ (9517 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 6637. -/
theorem theta6204_psi_6637_bounds :
    (6632032 : ℝ) / 1000 ≤ Chebyshev.psi 6637 ∧ Chebyshev.psi 6637 ≤ (6632726 : ℝ) / 1000 := by
  have hl : 2 ^ 9568 ≤ Nat.lcmUpto 6637 := by decide +kernel
  have hu : Nat.lcmUpto 6637 ≤ 2 ^ (9568 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 6679. -/
theorem theta6204_psi_6679_bounds :
    (6675700 : ℝ) / 1000 ≤ Chebyshev.psi 6679 ∧ Chebyshev.psi 6679 ≤ (6676394 : ℝ) / 1000 := by
  have hl : 2 ^ 9631 ≤ Nat.lcmUpto 6679 := by decide +kernel
  have hu : Nat.lcmUpto 6679 ≤ 2 ^ (9631 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 6719. -/
theorem theta6204_psi_6719_bounds :
    (6729072 : ℝ) / 1000 ≤ Chebyshev.psi 6719 ∧ Chebyshev.psi 6719 ≤ (6729766 : ℝ) / 1000 := by
  have hl : 2 ^ 9708 ≤ Nat.lcmUpto 6719 := by decide +kernel
  have hu : Nat.lcmUpto 6719 ≤ 2 ^ (9708 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 6779. -/
theorem theta6204_psi_6779_bounds :
    (6772741 : ℝ) / 1000 ≤ Chebyshev.psi 6779 ∧ Chebyshev.psi 6779 ≤ (6773435 : ℝ) / 1000 := by
  have hl : 2 ^ 9771 ≤ Nat.lcmUpto 6779 := by decide +kernel
  have hu : Nat.lcmUpto 6779 ≤ 2 ^ (9771 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 6823. -/
theorem theta6204_psi_6823_bounds :
    (6817102 : ℝ) / 1000 ≤ Chebyshev.psi 6823 ∧ Chebyshev.psi 6823 ≤ (6817796 : ℝ) / 1000 := by
  have hl : 2 ^ 9835 ≤ Nat.lcmUpto 6823 := by decide +kernel
  have hu : Nat.lcmUpto 6823 ≤ 2 ^ (9835 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- Every batch cell has a checked theta lower bound. -/
theorem theta6204_lower : ∀ r ∈ theta6204Cells, (r.lo : ℝ) / 1000 ≤ Chebyshev.theta r.a := by
  intro r hr
  simp only [theta6204Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change (6083055 : ℝ) / 1000 ≤ Chebyshev.theta (↑(6204 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_11368 (x := 6204) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 6203) (b := 6204) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta6204_psi_6203_bounds.1]
  · change (6131576 : ℝ) / 1000 ≤ Chebyshev.theta (↑(6248 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_11368 (x := 6248) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 6247) (b := 6248) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta6204_psi_6247_bounds.1]
  · change (6183562 : ℝ) / 1000 ≤ Chebyshev.theta (↑(6296 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_11368 (x := 6296) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 6287) (b := 6296) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta6204_psi_6287_bounds.1]
  · change (6253569 : ℝ) / 1000 ≤ Chebyshev.theta (↑(6348 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_11368 (x := 6348) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 6343) (b := 6348) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta6204_psi_6343_bounds.1]
  · change (6323577 : ℝ) / 1000 ≤ Chebyshev.theta (↑(6418 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_11368 (x := 6418) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 6397) (b := 6418) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta6204_psi_6397_bounds.1]
  · change (6385267 : ℝ) / 1000 ≤ Chebyshev.theta (↑(6488 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_11368 (x := 6488) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 6481) (b := 6488) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta6204_psi_6481_bounds.1]
  · change (6420618 : ℝ) / 1000 ≤ Chebyshev.theta (↑(6550 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_11368 (x := 6550) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 6547) (b := 6550) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta6204_psi_6547_bounds.1]
  · change (6483001 : ℝ) / 1000 ≤ Chebyshev.theta (↑(6585 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_11368 (x := 6585) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 6581) (b := 6585) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta6204_psi_6581_bounds.1]
  · change (6518352 : ℝ) / 1000 ≤ Chebyshev.theta (↑(6648 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_11368 (x := 6648) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 6637) (b := 6648) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta6204_psi_6637_bounds.1]
  · change (6562020 : ℝ) / 1000 ≤ Chebyshev.theta (↑(6683 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_11368 (x := 6683) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 6679) (b := 6683) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta6204_psi_6679_bounds.1]
  · change (6615392 : ℝ) / 1000 ≤ Chebyshev.theta (↑(6727 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_11368 (x := 6727) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 6719) (b := 6727) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta6204_psi_6719_bounds.1]
  · change (6659061 : ℝ) / 1000 ≤ Chebyshev.theta (↑(6780 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_11368 (x := 6780) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 6779) (b := 6780) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta6204_psi_6779_bounds.1]

/-- Every batch cell has a checked theta upper bound. -/
theorem theta6204_upper :
    ∀ r ∈ theta6204Cells, Chebyshev.theta (r.b - 1 : ℕ) ≤ (r.hi : ℝ) / 1000 := by
  intro r hr
  simp only [theta6204Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change Chebyshev.theta (↑(6247 : ℕ) : ℝ) ≤ (6245950 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 6247
    linarith only [hd, theta6204_psi_6247_bounds.2]
  · change Chebyshev.theta (↑(6295 : ℕ) : ℝ) ≤ (6297936 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 6295
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 6287) (b := 6295) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta6204_psi_6287_bounds.2]
  · change Chebyshev.theta (↑(6347 : ℕ) : ℝ) ≤ (6367944 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 6347
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 6343) (b := 6347) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta6204_psi_6343_bounds.2]
  · change Chebyshev.theta (↑(6417 : ℕ) : ℝ) ≤ (6437952 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 6417
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 6397) (b := 6417) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta6204_psi_6397_bounds.2]
  · change Chebyshev.theta (↑(6487 : ℕ) : ℝ) ≤ (6499642 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 6487
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 6481) (b := 6487) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta6204_psi_6481_bounds.2]
  · change Chebyshev.theta (↑(6549 : ℕ) : ℝ) ≤ (6534992 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 6549
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 6547) (b := 6549) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta6204_psi_6547_bounds.2]
  · change Chebyshev.theta (↑(6584 : ℕ) : ℝ) ≤ (6597375 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 6584
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 6581) (b := 6584) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta6204_psi_6581_bounds.2]
  · change Chebyshev.theta (↑(6647 : ℕ) : ℝ) ≤ (6632726 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 6647
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 6637) (b := 6647) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta6204_psi_6637_bounds.2]
  · change Chebyshev.theta (↑(6682 : ℕ) : ℝ) ≤ (6676394 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 6682
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 6679) (b := 6682) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta6204_psi_6679_bounds.2]
  · change Chebyshev.theta (↑(6726 : ℕ) : ℝ) ≤ (6729766 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 6726
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 6719) (b := 6726) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta6204_psi_6719_bounds.2]
  · change Chebyshev.theta (↑(6779 : ℕ) : ℝ) ≤ (6773435 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 6779
    linarith only [hd, theta6204_psi_6779_bounds.2]
  · change Chebyshev.theta (↑(6823 : ℕ) : ℝ) ≤ (6817796 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 6823
    linarith only [hd, theta6204_psi_6823_bounds.2]

/-- The envelope bound applies at every cell a endpoint. -/
theorem theta6204_a :
    ∀ r ∈ theta6204Cells,
      (r.ca : ℝ) / 1000 ≤
        Real.sqrt r.a *
          (Real.log r.a * (Real.log r.a - Real.log (Real.log r.a)) / (8 * Real.pi)) := by
  intro r hr
  simp only [theta6204Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 6204 *
          (Real.log 6204 * (Real.log 6204 - Real.log (Real.log 6204)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 6248 *
          (Real.log 6248 * (Real.log 6248 - Real.log (Real.log 6248)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 6296 *
          (Real.log 6296 * (Real.log 6296 - Real.log (Real.log 6296)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 6348 *
          (Real.log 6348 * (Real.log 6348 - Real.log (Real.log 6348)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 6418 *
          (Real.log 6418 * (Real.log 6418 - Real.log (Real.log 6418)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 6488 *
          (Real.log 6488 * (Real.log 6488 - Real.log (Real.log 6488)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 6550 *
          (Real.log 6550 * (Real.log 6550 - Real.log (Real.log 6550)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 6585 *
          (Real.log 6585 * (Real.log 6585 - Real.log (Real.log 6585)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 6648 *
          (Real.log 6648 * (Real.log 6648 - Real.log (Real.log 6648)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 6683 *
          (Real.log 6683 * (Real.log 6683 - Real.log (Real.log 6683)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 6727 *
          (Real.log 6727 * (Real.log 6727 - Real.log (Real.log 6727)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 6780 *
          (Real.log 6780 * (Real.log 6780 - Real.log (Real.log 6780)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)

/-- The envelope bound applies at every cell b endpoint. -/
theorem theta6204_b :
    ∀ r ∈ theta6204Cells,
      (r.cb : ℝ) / 1000 ≤
        Real.sqrt r.b *
          (Real.log r.b * (Real.log r.b - Real.log (Real.log r.b)) / (8 * Real.pi)) := by
  intro r hr
  simp only [theta6204Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 6248 *
          (Real.log 6248 * (Real.log 6248 - Real.log (Real.log 6248)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 6296 *
          (Real.log 6296 * (Real.log 6296 - Real.log (Real.log 6296)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 6348 *
          (Real.log 6348 * (Real.log 6348 - Real.log (Real.log 6348)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 6418 *
          (Real.log 6418 * (Real.log 6418 - Real.log (Real.log 6418)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 6488 *
          (Real.log 6488 * (Real.log 6488 - Real.log (Real.log 6488)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 6550 *
          (Real.log 6550 * (Real.log 6550 - Real.log (Real.log 6550)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 6585 *
          (Real.log 6585 * (Real.log 6585 - Real.log (Real.log 6585)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 6648 *
          (Real.log 6648 * (Real.log 6648 - Real.log (Real.log 6648)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 6683 *
          (Real.log 6683 * (Real.log 6683 - Real.log (Real.log 6683)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 6727 *
          (Real.log 6727 * (Real.log 6727 - Real.log (Real.log 6727)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 6780 *
          (Real.log 6780 * (Real.log 6780 - Real.log (Real.log 6780)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)
  · change
      (165000 : ℝ) / 1000 ≤
        Real.sqrt 6824 *
          (Real.log 6824 * (Real.log 6824 - Real.log (Real.log 6824)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_165 (by norm_num only)

/-- The cells form a checked chain covering `[6204, 6824)`. -/
theorem theta6204_check : leeNosalChainCheck 6204 6824 theta6204Cells = true := by decide +kernel

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
