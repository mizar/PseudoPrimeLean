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
def theta24376Cells : List LeeNosalCell :=
  [⟨24376, 24568, 24203286, 24614350, 365000, 365000⟩,
    ⟨24568, 24753, 24388356, 24761297, 365000, 365000⟩,
    ⟨24753, 24900, 24535303, 24892995, 365000, 365000⟩,
    ⟨24900, 25032, 24667001, 25024693, 365000, 365000⟩,
    ⟨25032, 25163, 24798699, 25145994, 365000, 365000⟩,
    ⟨25163, 25295, 24930397, 25267988, 365000, 365000⟩,
    ⟨25295, 25406, 25041994, 25389289, 365000, 365000⟩,
    ⟨25406, 25528, 25163294, 25500885, 365000, 365000⟩,
    ⟨25528, 25639, 25274891, 25622879, 365000, 365000⟩,
    ⟨25639, 25771, 25406589, 25764974, 365000, 365000⟩,
    ⟨25771, 25914, 25549377, 25896672, 365000, 365000⟩,
    ⟨25914, 26035, 25670678, 26039461, 365000, 365000⟩]

/-- The kernel-checked prefix bounds for 24373. -/
theorem theta24376_psi_24373_bounds :
    (24428586 : ℝ) / 1000 ≤ Chebyshev.psi 24373 ∧ Chebyshev.psi 24373 ≤ (24429280 : ℝ) / 1000 := by
  have hl : 2 ^ 35243 ≤ Nat.lcmUpto 24373 := by decide +kernel
  have hu : Nat.lcmUpto 24373 ≤ 2 ^ (35243 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 24551. -/
theorem theta24376_psi_24551_bounds :
    (24613656 : ℝ) / 1000 ≤ Chebyshev.psi 24551 ∧ Chebyshev.psi 24551 ≤ (24614350 : ℝ) / 1000 := by
  have hl : 2 ^ 35510 ≤ Nat.lcmUpto 24551 := by decide +kernel
  have hu : Nat.lcmUpto 24551 ≤ 2 ^ (35510 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 24749. -/
theorem theta24376_psi_24749_bounds :
    (24760603 : ℝ) / 1000 ≤ Chebyshev.psi 24749 ∧ Chebyshev.psi 24749 ≤ (24761297 : ℝ) / 1000 := by
  have hl : 2 ^ 35722 ≤ Nat.lcmUpto 24749 := by decide +kernel
  have hu : Nat.lcmUpto 24749 ≤ 2 ^ (35722 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 24889. -/
theorem theta24376_psi_24889_bounds :
    (24892301 : ℝ) / 1000 ≤ Chebyshev.psi 24889 ∧ Chebyshev.psi 24889 ≤ (24892995 : ℝ) / 1000 := by
  have hl : 2 ^ 35912 ≤ Nat.lcmUpto 24889 := by decide +kernel
  have hu : Nat.lcmUpto 24889 ≤ 2 ^ (35912 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 25031. -/
theorem theta24376_psi_25031_bounds :
    (25023999 : ℝ) / 1000 ≤ Chebyshev.psi 25031 ∧ Chebyshev.psi 25031 ≤ (25024693 : ℝ) / 1000 := by
  have hl : 2 ^ 36102 ≤ Nat.lcmUpto 25031 := by decide +kernel
  have hu : Nat.lcmUpto 25031 ≤ 2 ^ (36102 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 25153. -/
theorem theta24376_psi_25153_bounds :
    (25145300 : ℝ) / 1000 ≤ Chebyshev.psi 25153 ∧ Chebyshev.psi 25153 ≤ (25145994 : ℝ) / 1000 := by
  have hl : 2 ^ 36277 ≤ Nat.lcmUpto 25153 := by decide +kernel
  have hu : Nat.lcmUpto 25153 ≤ 2 ^ (36277 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 25163. -/
theorem theta24376_psi_25163_bounds :
    (25155697 : ℝ) / 1000 ≤ Chebyshev.psi 25163 ∧ Chebyshev.psi 25163 ≤ (25156391 : ℝ) / 1000 := by
  have hl : 2 ^ 36292 ≤ Nat.lcmUpto 25163 := by decide +kernel
  have hu : Nat.lcmUpto 25163 ≤ 2 ^ (36292 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 25261. -/
theorem theta24376_psi_25261_bounds :
    (25267294 : ℝ) / 1000 ≤ Chebyshev.psi 25261 ∧ Chebyshev.psi 25261 ≤ (25267988 : ℝ) / 1000 := by
  have hl : 2 ^ 36453 ≤ Nat.lcmUpto 25261 := by decide +kernel
  have hu : Nat.lcmUpto 25261 ≤ 2 ^ (36453 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 25391. -/
theorem theta24376_psi_25391_bounds :
    (25388594 : ℝ) / 1000 ≤ Chebyshev.psi 25391 ∧ Chebyshev.psi 25391 ≤ (25389289 : ℝ) / 1000 := by
  have hl : 2 ^ 36628 ≤ Nat.lcmUpto 25391 := by decide +kernel
  have hu : Nat.lcmUpto 25391 ≤ 2 ^ (36628 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 25523. -/
theorem theta24376_psi_25523_bounds :
    (25500191 : ℝ) / 1000 ≤ Chebyshev.psi 25523 ∧ Chebyshev.psi 25523 ≤ (25500885 : ℝ) / 1000 := by
  have hl : 2 ^ 36789 ≤ Nat.lcmUpto 25523 := by decide +kernel
  have hu : Nat.lcmUpto 25523 ≤ 2 ^ (36789 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 25633. -/
theorem theta24376_psi_25633_bounds :
    (25622185 : ℝ) / 1000 ≤ Chebyshev.psi 25633 ∧ Chebyshev.psi 25633 ≤ (25622879 : ℝ) / 1000 := by
  have hl : 2 ^ 36965 ≤ Nat.lcmUpto 25633 := by decide +kernel
  have hu : Nat.lcmUpto 25633 ≤ 2 ^ (36965 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 25639. -/
theorem theta24376_psi_25639_bounds :
    (25631889 : ℝ) / 1000 ≤ Chebyshev.psi 25639 ∧ Chebyshev.psi 25639 ≤ (25632583 : ℝ) / 1000 := by
  have hl : 2 ^ 36979 ≤ Nat.lcmUpto 25639 := by decide +kernel
  have hu : Nat.lcmUpto 25639 ≤ 2 ^ (36979 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 25763. -/
theorem theta24376_psi_25763_bounds :
    (25764280 : ℝ) / 1000 ≤ Chebyshev.psi 25763 ∧ Chebyshev.psi 25763 ≤ (25764974 : ℝ) / 1000 := by
  have hl : 2 ^ 37170 ≤ Nat.lcmUpto 25763 := by decide +kernel
  have hu : Nat.lcmUpto 25763 ≤ 2 ^ (37170 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 25771. -/
theorem theta24376_psi_25771_bounds :
    (25774677 : ℝ) / 1000 ≤ Chebyshev.psi 25771 ∧ Chebyshev.psi 25771 ≤ (25775372 : ℝ) / 1000 := by
  have hl : 2 ^ 37185 ≤ Nat.lcmUpto 25771 := by decide +kernel
  have hu : Nat.lcmUpto 25771 ≤ 2 ^ (37185 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 25913. -/
theorem theta24376_psi_25913_bounds :
    (25895978 : ℝ) / 1000 ≤ Chebyshev.psi 25913 ∧ Chebyshev.psi 25913 ≤ (25896672 : ℝ) / 1000 := by
  have hl : 2 ^ 37360 ≤ Nat.lcmUpto 25913 := by decide +kernel
  have hu : Nat.lcmUpto 25913 ≤ 2 ^ (37360 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 26029. -/
theorem theta24376_psi_26029_bounds :
    (26038766 : ℝ) / 1000 ≤ Chebyshev.psi 26029 ∧ Chebyshev.psi 26029 ≤ (26039461 : ℝ) / 1000 := by
  have hl : 2 ^ 37566 ≤ Nat.lcmUpto 26029 := by decide +kernel
  have hu : Nat.lcmUpto 26029 ≤ 2 ^ (37566 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- Every batch cell has a checked theta lower bound. -/
theorem theta24376_lower : ∀ r ∈ theta24376Cells, (r.lo : ℝ) / 1000 ≤ Chebyshev.theta r.a := by
  intro r hr
  simp only [theta24376Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change (24203286 : ℝ) / 1000 ≤ Chebyshev.theta (↑(24376 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 24376) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 24373) (b := 24376) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta24376_psi_24373_bounds.1]
  · change (24388356 : ℝ) / 1000 ≤ Chebyshev.theta (↑(24568 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 24568) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 24551) (b := 24568) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta24376_psi_24551_bounds.1]
  · change (24535303 : ℝ) / 1000 ≤ Chebyshev.theta (↑(24753 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 24753) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 24749) (b := 24753) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta24376_psi_24749_bounds.1]
  · change (24667001 : ℝ) / 1000 ≤ Chebyshev.theta (↑(24900 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 24900) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 24889) (b := 24900) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta24376_psi_24889_bounds.1]
  · change (24798699 : ℝ) / 1000 ≤ Chebyshev.theta (↑(25032 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 25032) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 25031) (b := 25032) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta24376_psi_25031_bounds.1]
  · change (24930397 : ℝ) / 1000 ≤ Chebyshev.theta (↑(25163 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 25163) (by norm_num only) (by norm_num only)
    linarith only [hd, theta24376_psi_25163_bounds.1]
  · change (25041994 : ℝ) / 1000 ≤ Chebyshev.theta (↑(25295 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 25295) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 25261) (b := 25295) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta24376_psi_25261_bounds.1]
  · change (25163294 : ℝ) / 1000 ≤ Chebyshev.theta (↑(25406 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 25406) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 25391) (b := 25406) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta24376_psi_25391_bounds.1]
  · change (25274891 : ℝ) / 1000 ≤ Chebyshev.theta (↑(25528 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 25528) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 25523) (b := 25528) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta24376_psi_25523_bounds.1]
  · change (25406589 : ℝ) / 1000 ≤ Chebyshev.theta (↑(25639 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 25639) (by norm_num only) (by norm_num only)
    linarith only [hd, theta24376_psi_25639_bounds.1]
  · change (25549377 : ℝ) / 1000 ≤ Chebyshev.theta (↑(25771 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 25771) (by norm_num only) (by norm_num only)
    linarith only [hd, theta24376_psi_25771_bounds.1]
  · change (25670678 : ℝ) / 1000 ≤ Chebyshev.theta (↑(25914 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_22530 (x := 25914) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 25913) (b := 25914) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta24376_psi_25913_bounds.1]

/-- Every batch cell has a checked theta upper bound. -/
theorem theta24376_upper :
    ∀ r ∈ theta24376Cells, Chebyshev.theta (r.b - 1 : ℕ) ≤ (r.hi : ℝ) / 1000 := by
  intro r hr
  simp only [theta24376Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change Chebyshev.theta (↑(24567 : ℕ) : ℝ) ≤ (24614350 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 24567
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 24551) (b := 24567) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta24376_psi_24551_bounds.2]
  · change Chebyshev.theta (↑(24752 : ℕ) : ℝ) ≤ (24761297 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 24752
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 24749) (b := 24752) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta24376_psi_24749_bounds.2]
  · change Chebyshev.theta (↑(24899 : ℕ) : ℝ) ≤ (24892995 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 24899
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 24889) (b := 24899) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta24376_psi_24889_bounds.2]
  · change Chebyshev.theta (↑(25031 : ℕ) : ℝ) ≤ (25024693 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 25031
    linarith only [hd, theta24376_psi_25031_bounds.2]
  · change Chebyshev.theta (↑(25162 : ℕ) : ℝ) ≤ (25145994 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 25162
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 25153) (b := 25162) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta24376_psi_25153_bounds.2]
  · change Chebyshev.theta (↑(25294 : ℕ) : ℝ) ≤ (25267988 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 25294
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 25261) (b := 25294) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta24376_psi_25261_bounds.2]
  · change Chebyshev.theta (↑(25405 : ℕ) : ℝ) ≤ (25389289 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 25405
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 25391) (b := 25405) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta24376_psi_25391_bounds.2]
  · change Chebyshev.theta (↑(25527 : ℕ) : ℝ) ≤ (25500885 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 25527
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 25523) (b := 25527) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta24376_psi_25523_bounds.2]
  · change Chebyshev.theta (↑(25638 : ℕ) : ℝ) ≤ (25622879 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 25638
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 25633) (b := 25638) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta24376_psi_25633_bounds.2]
  · change Chebyshev.theta (↑(25770 : ℕ) : ℝ) ≤ (25764974 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 25770
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 25763) (b := 25770) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta24376_psi_25763_bounds.2]
  · change Chebyshev.theta (↑(25913 : ℕ) : ℝ) ≤ (25896672 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 25913
    linarith only [hd, theta24376_psi_25913_bounds.2]
  · change Chebyshev.theta (↑(26034 : ℕ) : ℝ) ≤ (26039461 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 26034
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 26029) (b := 26034) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta24376_psi_26029_bounds.2]

/-- The envelope bound applies at every cell a endpoint. -/
theorem theta24376_a :
    ∀ r ∈ theta24376Cells,
      (r.ca : ℝ) / 1000 ≤
        Real.sqrt r.a *
          (Real.log r.a * (Real.log r.a - Real.log (Real.log r.a)) / (8 * Real.pi)) := by
  intro r hr
  simp only [theta24376Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 24376 *
          (Real.log 24376 * (Real.log 24376 - Real.log (Real.log 24376)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 24568 *
          (Real.log 24568 * (Real.log 24568 - Real.log (Real.log 24568)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 24753 *
          (Real.log 24753 * (Real.log 24753 - Real.log (Real.log 24753)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 24900 *
          (Real.log 24900 * (Real.log 24900 - Real.log (Real.log 24900)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 25032 *
          (Real.log 25032 * (Real.log 25032 - Real.log (Real.log 25032)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 25163 *
          (Real.log 25163 * (Real.log 25163 - Real.log (Real.log 25163)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 25295 *
          (Real.log 25295 * (Real.log 25295 - Real.log (Real.log 25295)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 25406 *
          (Real.log 25406 * (Real.log 25406 - Real.log (Real.log 25406)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 25528 *
          (Real.log 25528 * (Real.log 25528 - Real.log (Real.log 25528)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 25639 *
          (Real.log 25639 * (Real.log 25639 - Real.log (Real.log 25639)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 25771 *
          (Real.log 25771 * (Real.log 25771 - Real.log (Real.log 25771)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 25914 *
          (Real.log 25914 * (Real.log 25914 - Real.log (Real.log 25914)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)

/-- The envelope bound applies at every cell b endpoint. -/
theorem theta24376_b :
    ∀ r ∈ theta24376Cells,
      (r.cb : ℝ) / 1000 ≤
        Real.sqrt r.b *
          (Real.log r.b * (Real.log r.b - Real.log (Real.log r.b)) / (8 * Real.pi)) := by
  intro r hr
  simp only [theta24376Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 24568 *
          (Real.log 24568 * (Real.log 24568 - Real.log (Real.log 24568)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 24753 *
          (Real.log 24753 * (Real.log 24753 - Real.log (Real.log 24753)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 24900 *
          (Real.log 24900 * (Real.log 24900 - Real.log (Real.log 24900)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 25032 *
          (Real.log 25032 * (Real.log 25032 - Real.log (Real.log 25032)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 25163 *
          (Real.log 25163 * (Real.log 25163 - Real.log (Real.log 25163)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 25295 *
          (Real.log 25295 * (Real.log 25295 - Real.log (Real.log 25295)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 25406 *
          (Real.log 25406 * (Real.log 25406 - Real.log (Real.log 25406)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 25528 *
          (Real.log 25528 * (Real.log 25528 - Real.log (Real.log 25528)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 25639 *
          (Real.log 25639 * (Real.log 25639 - Real.log (Real.log 25639)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 25771 *
          (Real.log 25771 * (Real.log 25771 - Real.log (Real.log 25771)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 25914 *
          (Real.log 25914 * (Real.log 25914 - Real.log (Real.log 25914)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)
  · change
      (365000 : ℝ) / 1000 ≤
        Real.sqrt 26035 *
          (Real.log 26035 * (Real.log 26035 - Real.log (Real.log 26035)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_365 (by norm_num only)

/-- The cells form a checked chain covering `[24376, 26035)`. -/
theorem theta24376_check : leeNosalChainCheck 24376 26035 theta24376Cells = true := by
  decide +kernel

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
