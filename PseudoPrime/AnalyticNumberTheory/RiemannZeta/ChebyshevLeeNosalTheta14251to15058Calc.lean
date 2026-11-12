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
def theta14251Cells : List LeeNosalCell :=
  [⟨14251, 14327, 14072251, 14278832, 255000, 255000⟩,
    ⟨14327, 14384, 14129782, 14317649, 255000, 255000⟩,
    ⟨14384, 14413, 14158895, 14365476, 255000, 255000⟩,
    ⟨14413, 14461, 14206722, 14423007, 255000, 255000⟩,
    ⟨14461, 14528, 14273264, 14470834, 255000, 255000⟩,
    ⟨14528, 14567, 14312080, 14547080, 255000, 255000⟩,
    ⟨14567, 14643, 14388326, 14617088, 255000, 255000⟩,
    ⟨14643, 14713, 14458334, 14664915, 255000, 255000⟩,
    ⟨14713, 14770, 14515865, 14760570, 255000, 255000⟩,
    ⟨14770, 14856, 14601816, 14856917, 255000, 255000⟩,
    ⟨14856, 14953, 14698163, 14962276, 255000, 255000⟩,
    ⟨14953, 15058, 14803521, 15030204, 255000, 255000⟩]

/-- The kernel-checked prefix bounds for 14251. -/
theorem theta14251_psi_14251_bounds :
    (14230311 : ℝ) / 1000 ≤ Chebyshev.psi 14251 ∧ Chebyshev.psi 14251 ≤ (14231005 : ℝ) / 1000 := by
  have hl : 2 ^ 20530 ≤ Nat.lcmUpto 14251 := by decide +kernel
  have hu : Nat.lcmUpto 14251 ≤ 2 ^ (20530 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 14323. -/
theorem theta14251_psi_14323_bounds :
    (14278138 : ℝ) / 1000 ≤ Chebyshev.psi 14323 ∧ Chebyshev.psi 14323 ≤ (14278832 : ℝ) / 1000 := by
  have hl : 2 ^ 20599 ≤ Nat.lcmUpto 14323 := by decide +kernel
  have hu : Nat.lcmUpto 14323 ≤ 2 ^ (20599 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 14327. -/
theorem theta14251_psi_14327_bounds :
    (14287842 : ℝ) / 1000 ≤ Chebyshev.psi 14327 ∧ Chebyshev.psi 14327 ≤ (14288536 : ℝ) / 1000 := by
  have hl : 2 ^ 20613 ≤ Nat.lcmUpto 14327 := by decide +kernel
  have hu : Nat.lcmUpto 14327 ≤ 2 ^ (20613 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 14369. -/
theorem theta14251_psi_14369_bounds :
    (14316955 : ℝ) / 1000 ≤ Chebyshev.psi 14369 ∧ Chebyshev.psi 14369 ≤ (14317649 : ℝ) / 1000 := by
  have hl : 2 ^ 20655 ≤ Nat.lcmUpto 14369 := by decide +kernel
  have hu : Nat.lcmUpto 14369 ≤ 2 ^ (20655 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 14411. -/
theorem theta14251_psi_14411_bounds :
    (14364782 : ℝ) / 1000 ≤ Chebyshev.psi 14411 ∧ Chebyshev.psi 14411 ≤ (14365476 : ℝ) / 1000 := by
  have hl : 2 ^ 20724 ≤ Nat.lcmUpto 14411 := by decide +kernel
  have hu : Nat.lcmUpto 14411 ≤ 2 ^ (20724 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 14449. -/
theorem theta14251_psi_14449_bounds :
    (14422313 : ℝ) / 1000 ≤ Chebyshev.psi 14449 ∧ Chebyshev.psi 14449 ≤ (14423007 : ℝ) / 1000 := by
  have hl : 2 ^ 20807 ≤ Nat.lcmUpto 14449 := by decide +kernel
  have hu : Nat.lcmUpto 14449 ≤ 2 ^ (20807 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 14461. -/
theorem theta14251_psi_14461_bounds :
    (14431324 : ℝ) / 1000 ≤ Chebyshev.psi 14461 ∧ Chebyshev.psi 14461 ≤ (14432018 : ℝ) / 1000 := by
  have hl : 2 ^ 20820 ≤ Nat.lcmUpto 14461 := by decide +kernel
  have hu : Nat.lcmUpto 14461 ≤ 2 ^ (20820 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 14519. -/
theorem theta14251_psi_14519_bounds :
    (14470140 : ℝ) / 1000 ≤ Chebyshev.psi 14519 ∧ Chebyshev.psi 14519 ≤ (14470834 : ℝ) / 1000 := by
  have hl : 2 ^ 20876 ≤ Nat.lcmUpto 14519 := by decide +kernel
  have hu : Nat.lcmUpto 14519 ≤ 2 ^ (20876 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 14563. -/
theorem theta14251_psi_14563_bounds :
    (14546386 : ℝ) / 1000 ≤ Chebyshev.psi 14563 ∧ Chebyshev.psi 14563 ≤ (14547080 : ℝ) / 1000 := by
  have hl : 2 ^ 20986 ≤ Nat.lcmUpto 14563 := by decide +kernel
  have hu : Nat.lcmUpto 14563 ≤ 2 ^ (20986 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 14641. -/
theorem theta14251_psi_14641_bounds :
    (14616394 : ℝ) / 1000 ≤ Chebyshev.psi 14641 ∧ Chebyshev.psi 14641 ≤ (14617088 : ℝ) / 1000 := by
  have hl : 2 ^ 21087 ≤ Nat.lcmUpto 14641 := by decide +kernel
  have hu : Nat.lcmUpto 14641 ≤ 2 ^ (21087 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 14699. -/
theorem theta14251_psi_14699_bounds :
    (14664221 : ℝ) / 1000 ≤ Chebyshev.psi 14699 ∧ Chebyshev.psi 14699 ≤ (14664915 : ℝ) / 1000 := by
  have hl : 2 ^ 21156 ≤ Nat.lcmUpto 14699 := by decide +kernel
  have hu : Nat.lcmUpto 14699 ≤ 2 ^ (21156 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 14713. -/
theorem theta14251_psi_14713_bounds :
    (14673925 : ℝ) / 1000 ≤ Chebyshev.psi 14713 ∧ Chebyshev.psi 14713 ≤ (14674619 : ℝ) / 1000 := by
  have hl : 2 ^ 21170 ≤ Nat.lcmUpto 14713 := by decide +kernel
  have hu : Nat.lcmUpto 14713 ≤ 2 ^ (21170 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 14767. -/
theorem theta14251_psi_14767_bounds :
    (14759876 : ℝ) / 1000 ≤ Chebyshev.psi 14767 ∧ Chebyshev.psi 14767 ≤ (14760570 : ℝ) / 1000 := by
  have hl : 2 ^ 21294 ≤ Nat.lcmUpto 14767 := by decide +kernel
  have hu : Nat.lcmUpto 14767 ≤ 2 ^ (21294 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 14851. -/
theorem theta14251_psi_14851_bounds :
    (14856223 : ℝ) / 1000 ≤ Chebyshev.psi 14851 ∧ Chebyshev.psi 14851 ≤ (14856917 : ℝ) / 1000 := by
  have hl : 2 ^ 21433 ≤ Nat.lcmUpto 14851 := by decide +kernel
  have hu : Nat.lcmUpto 14851 ≤ 2 ^ (21433 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 14951. -/
theorem theta14251_psi_14951_bounds :
    (14961581 : ℝ) / 1000 ≤ Chebyshev.psi 14951 ∧ Chebyshev.psi 14951 ≤ (14962276 : ℝ) / 1000 := by
  have hl : 2 ^ 21585 ≤ Nat.lcmUpto 14951 := by decide +kernel
  have hu : Nat.lcmUpto 14951 ≤ 2 ^ (21585 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 15053. -/
theorem theta14251_psi_15053_bounds :
    (15029510 : ℝ) / 1000 ≤ Chebyshev.psi 15053 ∧ Chebyshev.psi 15053 ≤ (15030204 : ℝ) / 1000 := by
  have hl : 2 ^ 21683 ≤ Nat.lcmUpto 15053 := by decide +kernel
  have hu : Nat.lcmUpto 15053 ≤ 2 ^ (21683 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- Every batch cell has a checked theta lower bound. -/
theorem theta14251_lower : ∀ r ∈ theta14251Cells, (r.lo : ℝ) / 1000 ≤ Chebyshev.theta r.a := by
  intro r hr
  simp only [theta14251Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change (14072251 : ℝ) / 1000 ≤ Chebyshev.theta (↑(14251 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 14251) (by norm_num only) (by norm_num only)
    linarith only [hd, theta14251_psi_14251_bounds.1]
  · change (14129782 : ℝ) / 1000 ≤ Chebyshev.theta (↑(14327 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 14327) (by norm_num only) (by norm_num only)
    linarith only [hd, theta14251_psi_14327_bounds.1]
  · change (14158895 : ℝ) / 1000 ≤ Chebyshev.theta (↑(14384 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 14384) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 14369) (b := 14384) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta14251_psi_14369_bounds.1]
  · change (14206722 : ℝ) / 1000 ≤ Chebyshev.theta (↑(14413 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 14413) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 14411) (b := 14413) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta14251_psi_14411_bounds.1]
  · change (14273264 : ℝ) / 1000 ≤ Chebyshev.theta (↑(14461 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 14461) (by norm_num only) (by norm_num only)
    linarith only [hd, theta14251_psi_14461_bounds.1]
  · change (14312080 : ℝ) / 1000 ≤ Chebyshev.theta (↑(14528 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 14528) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 14519) (b := 14528) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta14251_psi_14519_bounds.1]
  · change (14388326 : ℝ) / 1000 ≤ Chebyshev.theta (↑(14567 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 14567) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 14563) (b := 14567) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta14251_psi_14563_bounds.1]
  · change (14458334 : ℝ) / 1000 ≤ Chebyshev.theta (↑(14643 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 14643) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 14641) (b := 14643) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta14251_psi_14641_bounds.1]
  · change (14515865 : ℝ) / 1000 ≤ Chebyshev.theta (↑(14713 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 14713) (by norm_num only) (by norm_num only)
    linarith only [hd, theta14251_psi_14713_bounds.1]
  · change (14601816 : ℝ) / 1000 ≤ Chebyshev.theta (↑(14770 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 14770) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 14767) (b := 14770) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta14251_psi_14767_bounds.1]
  · change (14698163 : ℝ) / 1000 ≤ Chebyshev.theta (↑(14856 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 14856) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 14851) (b := 14856) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta14251_psi_14851_bounds.1]
  · change (14803521 : ℝ) / 1000 ≤ Chebyshev.theta (↑(14953 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 14953) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 14951) (b := 14953) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta14251_psi_14951_bounds.1]

/-- Every batch cell has a checked theta upper bound. -/
theorem theta14251_upper :
    ∀ r ∈ theta14251Cells, Chebyshev.theta (r.b - 1 : ℕ) ≤ (r.hi : ℝ) / 1000 := by
  intro r hr
  simp only [theta14251Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change Chebyshev.theta (↑(14326 : ℕ) : ℝ) ≤ (14278832 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 14326
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 14323) (b := 14326) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta14251_psi_14323_bounds.2]
  · change Chebyshev.theta (↑(14383 : ℕ) : ℝ) ≤ (14317649 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 14383
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 14369) (b := 14383) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta14251_psi_14369_bounds.2]
  · change Chebyshev.theta (↑(14412 : ℕ) : ℝ) ≤ (14365476 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 14412
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 14411) (b := 14412) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta14251_psi_14411_bounds.2]
  · change Chebyshev.theta (↑(14460 : ℕ) : ℝ) ≤ (14423007 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 14460
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 14449) (b := 14460) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta14251_psi_14449_bounds.2]
  · change Chebyshev.theta (↑(14527 : ℕ) : ℝ) ≤ (14470834 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 14527
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 14519) (b := 14527) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta14251_psi_14519_bounds.2]
  · change Chebyshev.theta (↑(14566 : ℕ) : ℝ) ≤ (14547080 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 14566
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 14563) (b := 14566) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta14251_psi_14563_bounds.2]
  · change Chebyshev.theta (↑(14642 : ℕ) : ℝ) ≤ (14617088 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 14642
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 14641) (b := 14642) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta14251_psi_14641_bounds.2]
  · change Chebyshev.theta (↑(14712 : ℕ) : ℝ) ≤ (14664915 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 14712
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 14699) (b := 14712) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta14251_psi_14699_bounds.2]
  · change Chebyshev.theta (↑(14769 : ℕ) : ℝ) ≤ (14760570 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 14769
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 14767) (b := 14769) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta14251_psi_14767_bounds.2]
  · change Chebyshev.theta (↑(14855 : ℕ) : ℝ) ≤ (14856917 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 14855
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 14851) (b := 14855) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta14251_psi_14851_bounds.2]
  · change Chebyshev.theta (↑(14952 : ℕ) : ℝ) ≤ (14962276 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 14952
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 14951) (b := 14952) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta14251_psi_14951_bounds.2]
  · change Chebyshev.theta (↑(15057 : ℕ) : ℝ) ≤ (15030204 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 15057
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 15053) (b := 15057) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta14251_psi_15053_bounds.2]

/-- The envelope bound applies at every cell a endpoint. -/
theorem theta14251_a :
    ∀ r ∈ theta14251Cells,
      (r.ca : ℝ) / 1000 ≤
        Real.sqrt r.a *
          (Real.log r.a * (Real.log r.a - Real.log (Real.log r.a)) / (8 * Real.pi)) := by
  intro r hr
  simp only [theta14251Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 14251 *
          (Real.log 14251 * (Real.log 14251 - Real.log (Real.log 14251)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 14327 *
          (Real.log 14327 * (Real.log 14327 - Real.log (Real.log 14327)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 14384 *
          (Real.log 14384 * (Real.log 14384 - Real.log (Real.log 14384)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 14413 *
          (Real.log 14413 * (Real.log 14413 - Real.log (Real.log 14413)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 14461 *
          (Real.log 14461 * (Real.log 14461 - Real.log (Real.log 14461)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 14528 *
          (Real.log 14528 * (Real.log 14528 - Real.log (Real.log 14528)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 14567 *
          (Real.log 14567 * (Real.log 14567 - Real.log (Real.log 14567)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 14643 *
          (Real.log 14643 * (Real.log 14643 - Real.log (Real.log 14643)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 14713 *
          (Real.log 14713 * (Real.log 14713 - Real.log (Real.log 14713)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 14770 *
          (Real.log 14770 * (Real.log 14770 - Real.log (Real.log 14770)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 14856 *
          (Real.log 14856 * (Real.log 14856 - Real.log (Real.log 14856)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 14953 *
          (Real.log 14953 * (Real.log 14953 - Real.log (Real.log 14953)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)

/-- The envelope bound applies at every cell b endpoint. -/
theorem theta14251_b :
    ∀ r ∈ theta14251Cells,
      (r.cb : ℝ) / 1000 ≤
        Real.sqrt r.b *
          (Real.log r.b * (Real.log r.b - Real.log (Real.log r.b)) / (8 * Real.pi)) := by
  intro r hr
  simp only [theta14251Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 14327 *
          (Real.log 14327 * (Real.log 14327 - Real.log (Real.log 14327)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 14384 *
          (Real.log 14384 * (Real.log 14384 - Real.log (Real.log 14384)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 14413 *
          (Real.log 14413 * (Real.log 14413 - Real.log (Real.log 14413)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 14461 *
          (Real.log 14461 * (Real.log 14461 - Real.log (Real.log 14461)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 14528 *
          (Real.log 14528 * (Real.log 14528 - Real.log (Real.log 14528)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 14567 *
          (Real.log 14567 * (Real.log 14567 - Real.log (Real.log 14567)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 14643 *
          (Real.log 14643 * (Real.log 14643 - Real.log (Real.log 14643)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 14713 *
          (Real.log 14713 * (Real.log 14713 - Real.log (Real.log 14713)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 14770 *
          (Real.log 14770 * (Real.log 14770 - Real.log (Real.log 14770)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 14856 *
          (Real.log 14856 * (Real.log 14856 - Real.log (Real.log 14856)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 14953 *
          (Real.log 14953 * (Real.log 14953 - Real.log (Real.log 14953)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)
  · change
      (255000 : ℝ) / 1000 ≤
        Real.sqrt 15058 *
          (Real.log 15058 * (Real.log 15058 - Real.log (Real.log 15058)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_255 (by norm_num only)

/-- The cells form a checked chain covering `[14251, 15058)`. -/
theorem theta14251_check : leeNosalChainCheck 14251 15058 theta14251Cells = true := by
  decide +kernel

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
