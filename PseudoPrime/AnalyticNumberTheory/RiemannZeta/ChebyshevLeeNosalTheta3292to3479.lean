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
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSmallDefect3600
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalLogCheck
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalMonotone
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalChecker

/-! # Batch certificate for Lee–Nosal theta cells -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The local cells store endpoint bounds in thousandths. -/
private def batchCells : List LeeNosalCell :=
  [⟨3292, 3299, 3188111, 3260565, 111000, 111000⟩, ⟨3299, 3307, 3196428, 3277200, 111000, 111000⟩,
    ⟨3307, 3323, 3212371, 3301461, 111000, 111000⟩, ⟨3323, 3347, 3236631, 3333345, 111000, 111000⟩,
    ⟨3347, 3380, 3269209, 3374241, 111000, 111000⟩, ⟨3380, 3412, 3301787, 3398501, 111000, 111000⟩,
    ⟨3412, 3437, 3326047, 3415137, 111000, 111000⟩, ⟨3437, 3453, 3342683, 3422761, 111000, 111000⟩,
    ⟨3453, 3461, 3350307, 3431079, 111000, 111000⟩, ⟨3461, 3477, 3366943, 3463657, 111000, 111000⟩,
    ⟨3477, 3479, 3391203, 3463657, 111000, 111000⟩]

/-- The kernel-checked prefix bounds for 3271. -/
private theorem psi_3271_bounds :
    (3259871 : ℝ) / 1000 ≤ Chebyshev.psi 3271 ∧ Chebyshev.psi 3271 ≤ (3260565 : ℝ) / 1000 := by
  have hl : 2 ^ 4703 ≤ Nat.lcmUpto 3271 := by decide +kernel
  have hu : Nat.lcmUpto 3271 ≤ 2 ^ (4703 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 3299. -/
private theorem psi_3299_bounds :
    (3268188 : ℝ) / 1000 ≤ Chebyshev.psi 3299 ∧ Chebyshev.psi 3299 ≤ (3268883 : ℝ) / 1000 := by
  have hl : 2 ^ 4715 ≤ Nat.lcmUpto 3299 := by decide +kernel
  have hu : Nat.lcmUpto 3299 ≤ 2 ^ (4715 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 3301. -/
private theorem psi_3301_bounds :
    (3276506 : ℝ) / 1000 ≤ Chebyshev.psi 3301 ∧ Chebyshev.psi 3301 ≤ (3277200 : ℝ) / 1000 := by
  have hl : 2 ^ 4727 ≤ Nat.lcmUpto 3301 := by decide +kernel
  have hu : Nat.lcmUpto 3301 ≤ 2 ^ (4727 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 3307. -/
private theorem psi_3307_bounds :
    (3284131 : ℝ) / 1000 ≤ Chebyshev.psi 3307 ∧ Chebyshev.psi 3307 ≤ (3284825 : ℝ) / 1000 := by
  have hl : 2 ^ 4738 ≤ Nat.lcmUpto 3307 := by decide +kernel
  have hu : Nat.lcmUpto 3307 ≤ 2 ^ (4738 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 3319. -/
private theorem psi_3319_bounds :
    (3300766 : ℝ) / 1000 ≤ Chebyshev.psi 3319 ∧ Chebyshev.psi 3319 ≤ (3301461 : ℝ) / 1000 := by
  have hl : 2 ^ 4762 ≤ Nat.lcmUpto 3319 := by decide +kernel
  have hu : Nat.lcmUpto 3319 ≤ 2 ^ (4762 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 3323. -/
private theorem psi_3323_bounds :
    (3308391 : ℝ) / 1000 ≤ Chebyshev.psi 3323 ∧ Chebyshev.psi 3323 ≤ (3309085 : ℝ) / 1000 := by
  have hl : 2 ^ 4773 ≤ Nat.lcmUpto 3323 := by decide +kernel
  have hu : Nat.lcmUpto 3323 ≤ 2 ^ (4773 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 3343. -/
private theorem psi_3343_bounds :
    (3332651 : ℝ) / 1000 ≤ Chebyshev.psi 3343 ∧ Chebyshev.psi 3343 ≤ (3333345 : ℝ) / 1000 := by
  have hl : 2 ^ 4808 ≤ Nat.lcmUpto 3343 := by decide +kernel
  have hu : Nat.lcmUpto 3343 ≤ 2 ^ (4808 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 3347. -/
private theorem psi_3347_bounds :
    (3340969 : ℝ) / 1000 ≤ Chebyshev.psi 3347 ∧ Chebyshev.psi 3347 ≤ (3341663 : ℝ) / 1000 := by
  have hl : 2 ^ 4820 ≤ Nat.lcmUpto 3347 := by decide +kernel
  have hu : Nat.lcmUpto 3347 ≤ 2 ^ (4820 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 3373. -/
private theorem psi_3373_bounds :
    (3373547 : ℝ) / 1000 ≤ Chebyshev.psi 3373 ∧ Chebyshev.psi 3373 ≤ (3374241 : ℝ) / 1000 := by
  have hl : 2 ^ 4867 ≤ Nat.lcmUpto 3373 := by decide +kernel
  have hu : Nat.lcmUpto 3373 ≤ 2 ^ (4867 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 3407. -/
private theorem psi_3407_bounds :
    (3397807 : ℝ) / 1000 ≤ Chebyshev.psi 3407 ∧ Chebyshev.psi 3407 ≤ (3398501 : ℝ) / 1000 := by
  have hl : 2 ^ 4902 ≤ Nat.lcmUpto 3407 := by decide +kernel
  have hu : Nat.lcmUpto 3407 ≤ 2 ^ (4902 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 3433. -/
private theorem psi_3433_bounds :
    (3414443 : ℝ) / 1000 ≤ Chebyshev.psi 3433 ∧ Chebyshev.psi 3433 ≤ (3415137 : ℝ) / 1000 := by
  have hl : 2 ^ 4926 ≤ Nat.lcmUpto 3433 := by decide +kernel
  have hu : Nat.lcmUpto 3433 ≤ 2 ^ (4926 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 3449. -/
private theorem psi_3449_bounds :
    (3422067 : ℝ) / 1000 ≤ Chebyshev.psi 3449 ∧ Chebyshev.psi 3449 ≤ (3422761 : ℝ) / 1000 := by
  have hl : 2 ^ 4937 ≤ Nat.lcmUpto 3449 := by decide +kernel
  have hu : Nat.lcmUpto 3449 ≤ 2 ^ (4937 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 3457. -/
private theorem psi_3457_bounds :
    (3430385 : ℝ) / 1000 ≤ Chebyshev.psi 3457 ∧ Chebyshev.psi 3457 ≤ (3431079 : ℝ) / 1000 := by
  have hl : 2 ^ 4949 ≤ Nat.lcmUpto 3457 := by decide +kernel
  have hu : Nat.lcmUpto 3457 ≤ 2 ^ (4949 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 3461. -/
private theorem psi_3461_bounds :
    (3438703 : ℝ) / 1000 ≤ Chebyshev.psi 3461 ∧ Chebyshev.psi 3461 ≤ (3439397 : ℝ) / 1000 := by
  have hl : 2 ^ 4961 ≤ Nat.lcmUpto 3461 := by decide +kernel
  have hu : Nat.lcmUpto 3461 ≤ 2 ^ (4961 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 3469. -/
private theorem psi_3469_bounds :
    (3462963 : ℝ) / 1000 ≤ Chebyshev.psi 3469 ∧ Chebyshev.psi 3469 ≤ (3463657 : ℝ) / 1000 := by
  have hl : 2 ^ 4996 ≤ Nat.lcmUpto 3469 := by decide +kernel
  have hu : Nat.lcmUpto 3469 ≤ 2 ^ (4996 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- A rational certificate bounds the envelope from 3292 onward. -/
private theorem batch_envelope {t : ℝ} (ht : 3292 ≤ t) :
    (111 : ℝ) ≤
      Real.sqrt t * (Real.log t * (Real.log t - Real.log (Real.log t)) / (8 * Real.pi)) := by
  have h :=
    lee_nosal_envelope_of_log_checks (N := 3292) (lo := 8099 / 1000) (hi := 8100 / 1000) (vlo :=
      2091 / 1000) (vhi := 2092 / 1000) (c := 111) (j := 12) (k := 4) (n := 32) (m := 32)
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by decide +kernel) (by decide +kernel) (by norm_num only)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact
    h.trans
      (lee_nosal_envelope_mono (x := 3292) (y := t)
        (Real.exp_one_lt_three.le.trans (by norm_num only)) ht)

/-- Every batch cell has a checked theta lower bound. -/
private theorem batch_lower : ∀ r ∈ batchCells, (r.lo : ℝ) / 1000 ≤ Chebyshev.theta r.a := by
  intro r hr
  simp only [batchCells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change (3188111 : ℝ) / 1000 ≤ Chebyshev.theta (↑(3292 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_7176 (x := 3292) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3271) (b := 3292) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3271_bounds.1]
  · change (3196428 : ℝ) / 1000 ≤ Chebyshev.theta (↑(3299 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_7176 (x := 3299) (by norm_num only) (by norm_num only)
    linarith only [hd, psi_3299_bounds.1]
  · change (3212371 : ℝ) / 1000 ≤ Chebyshev.theta (↑(3307 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_7176 (x := 3307) (by norm_num only) (by norm_num only)
    linarith only [hd, psi_3307_bounds.1]
  · change (3236631 : ℝ) / 1000 ≤ Chebyshev.theta (↑(3323 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_7176 (x := 3323) (by norm_num only) (by norm_num only)
    linarith only [hd, psi_3323_bounds.1]
  · change (3269209 : ℝ) / 1000 ≤ Chebyshev.theta (↑(3347 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_7176 (x := 3347) (by norm_num only) (by norm_num only)
    linarith only [hd, psi_3347_bounds.1]
  · change (3301787 : ℝ) / 1000 ≤ Chebyshev.theta (↑(3380 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_7176 (x := 3380) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3373) (b := 3380) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3373_bounds.1]
  · change (3326047 : ℝ) / 1000 ≤ Chebyshev.theta (↑(3412 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_7176 (x := 3412) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3407) (b := 3412) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3407_bounds.1]
  · change (3342683 : ℝ) / 1000 ≤ Chebyshev.theta (↑(3437 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_7176 (x := 3437) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3433) (b := 3437) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3433_bounds.1]
  · change (3350307 : ℝ) / 1000 ≤ Chebyshev.theta (↑(3453 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_7176 (x := 3453) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3449) (b := 3453) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3449_bounds.1]
  · change (3366943 : ℝ) / 1000 ≤ Chebyshev.theta (↑(3461 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_7176 (x := 3461) (by norm_num only) (by norm_num only)
    linarith only [hd, psi_3461_bounds.1]
  · change (3391203 : ℝ) / 1000 ≤ Chebyshev.theta (↑(3477 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_7176 (x := 3477) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3469) (b := 3477) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3469_bounds.1]

/-- Every batch cell has a checked theta upper bound. -/
private theorem batch_upper :
    ∀ r ∈ batchCells, Chebyshev.theta (r.b - 1 : ℕ) ≤ (r.hi : ℝ) / 1000 := by
  intro r hr
  simp only [batchCells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change Chebyshev.theta (↑(3298 : ℕ) : ℝ) ≤ (3260565 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 3298
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3271) (b := 3298) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3271_bounds.2]
  · change Chebyshev.theta (↑(3306 : ℕ) : ℝ) ≤ (3277200 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 3306
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3301) (b := 3306) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3301_bounds.2]
  · change Chebyshev.theta (↑(3322 : ℕ) : ℝ) ≤ (3301461 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 3322
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3319) (b := 3322) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3319_bounds.2]
  · change Chebyshev.theta (↑(3346 : ℕ) : ℝ) ≤ (3333345 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 3346
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3343) (b := 3346) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3343_bounds.2]
  · change Chebyshev.theta (↑(3379 : ℕ) : ℝ) ≤ (3374241 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 3379
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3373) (b := 3379) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3373_bounds.2]
  · change Chebyshev.theta (↑(3411 : ℕ) : ℝ) ≤ (3398501 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 3411
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3407) (b := 3411) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3407_bounds.2]
  · change Chebyshev.theta (↑(3436 : ℕ) : ℝ) ≤ (3415137 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 3436
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3433) (b := 3436) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3433_bounds.2]
  · change Chebyshev.theta (↑(3452 : ℕ) : ℝ) ≤ (3422761 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 3452
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3449) (b := 3452) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3449_bounds.2]
  · change Chebyshev.theta (↑(3460 : ℕ) : ℝ) ≤ (3431079 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 3460
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3457) (b := 3460) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3457_bounds.2]
  · change Chebyshev.theta (↑(3476 : ℕ) : ℝ) ≤ (3463657 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 3476
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3469) (b := 3476) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3469_bounds.2]
  · change Chebyshev.theta (↑(3478 : ℕ) : ℝ) ≤ (3463657 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 3478
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3469) (b := 3478) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3469_bounds.2]

/-- The envelope bound applies at every cell a endpoint. -/
private theorem batch_a :
    ∀ r ∈ batchCells,
      (r.ca : ℝ) / 1000 ≤
        Real.sqrt r.a *
          (Real.log r.a * (Real.log r.a - Real.log (Real.log r.a)) / (8 * Real.pi)) := by
  intro r hr
  simp only [batchCells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change
      (111000 : ℝ) / 1000 ≤
        Real.sqrt 3292 *
          (Real.log 3292 * (Real.log 3292 - Real.log (Real.log 3292)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (111000 : ℝ) / 1000 ≤
        Real.sqrt 3299 *
          (Real.log 3299 * (Real.log 3299 - Real.log (Real.log 3299)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (111000 : ℝ) / 1000 ≤
        Real.sqrt 3307 *
          (Real.log 3307 * (Real.log 3307 - Real.log (Real.log 3307)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (111000 : ℝ) / 1000 ≤
        Real.sqrt 3323 *
          (Real.log 3323 * (Real.log 3323 - Real.log (Real.log 3323)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (111000 : ℝ) / 1000 ≤
        Real.sqrt 3347 *
          (Real.log 3347 * (Real.log 3347 - Real.log (Real.log 3347)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (111000 : ℝ) / 1000 ≤
        Real.sqrt 3380 *
          (Real.log 3380 * (Real.log 3380 - Real.log (Real.log 3380)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (111000 : ℝ) / 1000 ≤
        Real.sqrt 3412 *
          (Real.log 3412 * (Real.log 3412 - Real.log (Real.log 3412)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (111000 : ℝ) / 1000 ≤
        Real.sqrt 3437 *
          (Real.log 3437 * (Real.log 3437 - Real.log (Real.log 3437)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (111000 : ℝ) / 1000 ≤
        Real.sqrt 3453 *
          (Real.log 3453 * (Real.log 3453 - Real.log (Real.log 3453)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (111000 : ℝ) / 1000 ≤
        Real.sqrt 3461 *
          (Real.log 3461 * (Real.log 3461 - Real.log (Real.log 3461)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (111000 : ℝ) / 1000 ≤
        Real.sqrt 3477 *
          (Real.log 3477 * (Real.log 3477 - Real.log (Real.log 3477)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)

/-- The envelope bound applies at every cell b endpoint. -/
private theorem batch_b :
    ∀ r ∈ batchCells,
      (r.cb : ℝ) / 1000 ≤
        Real.sqrt r.b *
          (Real.log r.b * (Real.log r.b - Real.log (Real.log r.b)) / (8 * Real.pi)) := by
  intro r hr
  simp only [batchCells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change
      (111000 : ℝ) / 1000 ≤
        Real.sqrt 3299 *
          (Real.log 3299 * (Real.log 3299 - Real.log (Real.log 3299)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (111000 : ℝ) / 1000 ≤
        Real.sqrt 3307 *
          (Real.log 3307 * (Real.log 3307 - Real.log (Real.log 3307)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (111000 : ℝ) / 1000 ≤
        Real.sqrt 3323 *
          (Real.log 3323 * (Real.log 3323 - Real.log (Real.log 3323)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (111000 : ℝ) / 1000 ≤
        Real.sqrt 3347 *
          (Real.log 3347 * (Real.log 3347 - Real.log (Real.log 3347)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (111000 : ℝ) / 1000 ≤
        Real.sqrt 3380 *
          (Real.log 3380 * (Real.log 3380 - Real.log (Real.log 3380)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (111000 : ℝ) / 1000 ≤
        Real.sqrt 3412 *
          (Real.log 3412 * (Real.log 3412 - Real.log (Real.log 3412)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (111000 : ℝ) / 1000 ≤
        Real.sqrt 3437 *
          (Real.log 3437 * (Real.log 3437 - Real.log (Real.log 3437)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (111000 : ℝ) / 1000 ≤
        Real.sqrt 3453 *
          (Real.log 3453 * (Real.log 3453 - Real.log (Real.log 3453)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (111000 : ℝ) / 1000 ≤
        Real.sqrt 3461 *
          (Real.log 3461 * (Real.log 3461 - Real.log (Real.log 3461)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (111000 : ℝ) / 1000 ≤
        Real.sqrt 3477 *
          (Real.log 3477 * (Real.log 3477 - Real.log (Real.log 3477)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (111000 : ℝ) / 1000 ≤
        Real.sqrt 3479 *
          (Real.log 3479 * (Real.log 3479 - Real.log (Real.log 3479)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)

/-- The checked batch proves the Lee–Nosal theta estimate on `[3292, 3479)`. -/
theorem theta_lee_nosal_3292_3479 {x : ℝ} (ha : 3292 ≤ x) (hb : x < 3479) :
    |Chebyshev.theta x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  exact
    lee_nosal_chain_sound Chebyshev.theta_mono Chebyshev.theta_eq_theta_coe_floor
      (by decide +kernel) batch_lower batch_upper batch_a batch_b ha hb

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
