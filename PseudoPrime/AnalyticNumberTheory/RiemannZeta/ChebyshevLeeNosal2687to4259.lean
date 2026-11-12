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
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalLogCheck
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalMonotone
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalChecker

/-! # Batch certificate for Lee–Nosal psi cells -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The local cells store endpoint bounds in thousandths. -/
private def batchCells : List LeeNosalCell :=
  [⟨2687, 2767, 2679013, 2774669, 93000, 93000⟩, ⟨2767, 2843, 2781599, 2857846, 93000, 93000⟩,
    ⟨2843, 2917, 2864777, 2929240, 93000, 93000⟩, ⟨2917, 3011, 2936864, 3009646, 93000, 93000⟩,
    ⟨3011, 3109, 3016576, 3097675, 93000, 93000⟩, ⟨3109, 3198, 3105299, 3180160, 93000, 93000⟩,
    ⟨3198, 3272, 3179466, 3260565, 93000, 93000⟩, ⟨3272, 3352, 3259871, 3341663, 93000, 93000⟩,
    ⟨3352, 3433, 3340969, 3406819, 93000, 93000⟩, ⟨3433, 3507, 3414443, 3484451, 93000, 93000⟩,
    ⟨3507, 3576, 3483757, 3573867, 93000, 93000⟩, ⟨3576, 3666, 3573173, 3663976, 93000, 93000⟩,
    ⟨3666, 3756, 3663282, 3758938, 93000, 93000⟩, ⟨3756, 3847, 3758244, 3841422, 93000, 93000⟩,
    ⟨3847, 3923, 3849046, 3932224, 93000, 93000⟩, ⟨3923, 4013, 3939848, 4014709, 93000, 93000⟩,
    ⟨4013, 4093, 4022333, 4097887, 93000, 93000⟩, ⟨4093, 4177, 4105510, 4181757, 93000, 93000⟩,
    ⟨4177, 4259, 4189381, 4265628, 93000, 93000⟩]

/-- The kernel-checked prefix bounds for 2687. -/
private theorem psi_2687_bounds :
    (2679013 : ℝ) / 1000 ≤ Chebyshev.psi 2687 ∧ Chebyshev.psi 2687 ≤ (2679708 : ℝ) / 1000 := by
  have hl : 2 ^ 3865 ≤ Nat.lcmUpto 2687 := by decide +kernel
  have hu : Nat.lcmUpto 2687 ≤ 2 ^ (3865 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 2753. -/
private theorem psi_2753_bounds :
    (2773975 : ℝ) / 1000 ≤ Chebyshev.psi 2753 ∧ Chebyshev.psi 2753 ≤ (2774669 : ℝ) / 1000 := by
  have hl : 2 ^ 4002 ≤ Nat.lcmUpto 2753 := by decide +kernel
  have hu : Nat.lcmUpto 2753 ≤ 2 ^ (4002 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 2767. -/
private theorem psi_2767_bounds :
    (2781599 : ℝ) / 1000 ≤ Chebyshev.psi 2767 ∧ Chebyshev.psi 2767 ≤ (2782293 : ℝ) / 1000 := by
  have hl : 2 ^ 4013 ≤ Nat.lcmUpto 2767 := by decide +kernel
  have hu : Nat.lcmUpto 2767 ≤ 2 ^ (4013 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 2837. -/
private theorem psi_2837_bounds :
    (2857152 : ℝ) / 1000 ≤ Chebyshev.psi 2837 ∧ Chebyshev.psi 2837 ≤ (2857846 : ℝ) / 1000 := by
  have hl : 2 ^ 4122 ≤ Nat.lcmUpto 2837 := by decide +kernel
  have hu : Nat.lcmUpto 2837 ≤ 2 ^ (4122 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 2843. -/
private theorem psi_2843_bounds :
    (2864777 : ℝ) / 1000 ≤ Chebyshev.psi 2843 ∧ Chebyshev.psi 2843 ≤ (2865471 : ℝ) / 1000 := by
  have hl : 2 ^ 4133 ≤ Nat.lcmUpto 2843 := by decide +kernel
  have hu : Nat.lcmUpto 2843 ≤ 2 ^ (4133 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 2909. -/
private theorem psi_2909_bounds :
    (2928546 : ℝ) / 1000 ≤ Chebyshev.psi 2909 ∧ Chebyshev.psi 2909 ≤ (2929240 : ℝ) / 1000 := by
  have hl : 2 ^ 4225 ≤ Nat.lcmUpto 2909 := by decide +kernel
  have hu : Nat.lcmUpto 2909 ≤ 2 ^ (4225 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 2917. -/
private theorem psi_2917_bounds :
    (2936864 : ℝ) / 1000 ≤ Chebyshev.psi 2917 ∧ Chebyshev.psi 2917 ≤ (2937558 : ℝ) / 1000 := by
  have hl : 2 ^ 4237 ≤ Nat.lcmUpto 2917 := by decide +kernel
  have hu : Nat.lcmUpto 2917 ≤ 2 ^ (4237 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 3001. -/
private theorem psi_3001_bounds :
    (3008951 : ℝ) / 1000 ≤ Chebyshev.psi 3001 ∧ Chebyshev.psi 3001 ≤ (3009646 : ℝ) / 1000 := by
  have hl : 2 ^ 4341 ≤ Nat.lcmUpto 3001 := by decide +kernel
  have hu : Nat.lcmUpto 3001 ≤ 2 ^ (4341 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 3011. -/
private theorem psi_3011_bounds :
    (3016576 : ℝ) / 1000 ≤ Chebyshev.psi 3011 ∧ Chebyshev.psi 3011 ≤ (3017270 : ℝ) / 1000 := by
  have hl : 2 ^ 4352 ≤ Nat.lcmUpto 3011 := by decide +kernel
  have hu : Nat.lcmUpto 3011 ≤ 2 ^ (4352 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 3089. -/
private theorem psi_3089_bounds :
    (3096981 : ℝ) / 1000 ≤ Chebyshev.psi 3089 ∧ Chebyshev.psi 3089 ≤ (3097675 : ℝ) / 1000 := by
  have hl : 2 ^ 4468 ≤ Nat.lcmUpto 3089 := by decide +kernel
  have hu : Nat.lcmUpto 3089 ≤ 2 ^ (4468 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 3109. -/
private theorem psi_3109_bounds :
    (3105299 : ℝ) / 1000 ≤ Chebyshev.psi 3109 ∧ Chebyshev.psi 3109 ≤ (3105993 : ℝ) / 1000 := by
  have hl : 2 ^ 4480 ≤ Nat.lcmUpto 3109 := by decide +kernel
  have hu : Nat.lcmUpto 3109 ≤ 2 ^ (4480 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 3191. -/
private theorem psi_3191_bounds :
    (3179466 : ℝ) / 1000 ≤ Chebyshev.psi 3191 ∧ Chebyshev.psi 3191 ≤ (3180160 : ℝ) / 1000 := by
  have hl : 2 ^ 4587 ≤ Nat.lcmUpto 3191 := by decide +kernel
  have hu : Nat.lcmUpto 3191 ≤ 2 ^ (4587 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 3271. -/
private theorem psi_3271_bounds :
    (3259871 : ℝ) / 1000 ≤ Chebyshev.psi 3271 ∧ Chebyshev.psi 3271 ≤ (3260565 : ℝ) / 1000 := by
  have hl : 2 ^ 4703 ≤ Nat.lcmUpto 3271 := by decide +kernel
  have hu : Nat.lcmUpto 3271 ≤ 2 ^ (4703 + 1) := by decide +kernel
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

/-- The kernel-checked prefix bounds for 3413. -/
private theorem psi_3413_bounds :
    (3406125 : ℝ) / 1000 ≤ Chebyshev.psi 3413 ∧ Chebyshev.psi 3413 ≤ (3406819 : ℝ) / 1000 := by
  have hl : 2 ^ 4914 ≤ Nat.lcmUpto 3413 := by decide +kernel
  have hu : Nat.lcmUpto 3413 ≤ 2 ^ (4914 + 1) := by decide +kernel
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

/-- The kernel-checked prefix bounds for 3499. -/
private theorem psi_3499_bounds :
    (3483757 : ℝ) / 1000 ≤ Chebyshev.psi 3499 ∧ Chebyshev.psi 3499 ≤ (3484451 : ℝ) / 1000 := by
  have hl : 2 ^ 5026 ≤ Nat.lcmUpto 3499 := by decide +kernel
  have hu : Nat.lcmUpto 3499 ≤ 2 ^ (5026 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 3571. -/
private theorem psi_3571_bounds :
    (3573173 : ℝ) / 1000 ≤ Chebyshev.psi 3571 ∧ Chebyshev.psi 3571 ≤ (3573867 : ℝ) / 1000 := by
  have hl : 2 ^ 5155 ≤ Nat.lcmUpto 3571 := by decide +kernel
  have hu : Nat.lcmUpto 3571 ≤ 2 ^ (5155 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 3659. -/
private theorem psi_3659_bounds :
    (3663282 : ℝ) / 1000 ≤ Chebyshev.psi 3659 ∧ Chebyshev.psi 3659 ≤ (3663976 : ℝ) / 1000 := by
  have hl : 2 ^ 5285 ≤ Nat.lcmUpto 3659 := by decide +kernel
  have hu : Nat.lcmUpto 3659 ≤ 2 ^ (5285 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 3739. -/
private theorem psi_3739_bounds :
    (3758244 : ℝ) / 1000 ≤ Chebyshev.psi 3739 ∧ Chebyshev.psi 3739 ≤ (3758938 : ℝ) / 1000 := by
  have hl : 2 ^ 5422 ≤ Nat.lcmUpto 3739 := by decide +kernel
  have hu : Nat.lcmUpto 3739 ≤ 2 ^ (5422 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 3833. -/
private theorem psi_3833_bounds :
    (3840728 : ℝ) / 1000 ≤ Chebyshev.psi 3833 ∧ Chebyshev.psi 3833 ≤ (3841422 : ℝ) / 1000 := by
  have hl : 2 ^ 5541 ≤ Nat.lcmUpto 3833 := by decide +kernel
  have hu : Nat.lcmUpto 3833 ≤ 2 ^ (5541 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 3847. -/
private theorem psi_3847_bounds :
    (3849046 : ℝ) / 1000 ≤ Chebyshev.psi 3847 ∧ Chebyshev.psi 3847 ≤ (3849740 : ℝ) / 1000 := by
  have hl : 2 ^ 5553 ≤ Nat.lcmUpto 3847 := by decide +kernel
  have hu : Nat.lcmUpto 3847 ≤ 2 ^ (5553 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 3919. -/
private theorem psi_3919_bounds :
    (3931530 : ℝ) / 1000 ≤ Chebyshev.psi 3919 ∧ Chebyshev.psi 3919 ≤ (3932224 : ℝ) / 1000 := by
  have hl : 2 ^ 5672 ≤ Nat.lcmUpto 3919 := by decide +kernel
  have hu : Nat.lcmUpto 3919 ≤ 2 ^ (5672 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 3923. -/
private theorem psi_3923_bounds :
    (3939848 : ℝ) / 1000 ≤ Chebyshev.psi 3923 ∧ Chebyshev.psi 3923 ≤ (3940542 : ℝ) / 1000 := by
  have hl : 2 ^ 5684 ≤ Nat.lcmUpto 3923 := by decide +kernel
  have hu : Nat.lcmUpto 3923 ≤ 2 ^ (5684 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 4007. -/
private theorem psi_4007_bounds :
    (4014015 : ℝ) / 1000 ≤ Chebyshev.psi 4007 ∧ Chebyshev.psi 4007 ≤ (4014709 : ℝ) / 1000 := by
  have hl : 2 ^ 5791 ≤ Nat.lcmUpto 4007 := by decide +kernel
  have hu : Nat.lcmUpto 4007 ≤ 2 ^ (5791 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 4013. -/
private theorem psi_4013_bounds :
    (4022333 : ℝ) / 1000 ≤ Chebyshev.psi 4013 ∧ Chebyshev.psi 4013 ≤ (4023027 : ℝ) / 1000 := by
  have hl : 2 ^ 5803 ≤ Nat.lcmUpto 4013 := by decide +kernel
  have hu : Nat.lcmUpto 4013 ≤ 2 ^ (5803 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 4091. -/
private theorem psi_4091_bounds :
    (4097192 : ℝ) / 1000 ≤ Chebyshev.psi 4091 ∧ Chebyshev.psi 4091 ≤ (4097887 : ℝ) / 1000 := by
  have hl : 2 ^ 5911 ≤ Nat.lcmUpto 4091 := by decide +kernel
  have hu : Nat.lcmUpto 4091 ≤ 2 ^ (5911 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 4093. -/
private theorem psi_4093_bounds :
    (4105510 : ℝ) / 1000 ≤ Chebyshev.psi 4093 ∧ Chebyshev.psi 4093 ≤ (4106204 : ℝ) / 1000 := by
  have hl : 2 ^ 5923 ≤ Nat.lcmUpto 4093 := by decide +kernel
  have hu : Nat.lcmUpto 4093 ≤ 2 ^ (5923 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 4159. -/
private theorem psi_4159_bounds :
    (4181063 : ℝ) / 1000 ≤ Chebyshev.psi 4159 ∧ Chebyshev.psi 4159 ≤ (4181757 : ℝ) / 1000 := by
  have hl : 2 ^ 6032 ≤ Nat.lcmUpto 4159 := by decide +kernel
  have hu : Nat.lcmUpto 4159 ≤ 2 ^ (6032 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 4177. -/
private theorem psi_4177_bounds :
    (4189381 : ℝ) / 1000 ≤ Chebyshev.psi 4177 ∧ Chebyshev.psi 4177 ≤ (4190075 : ℝ) / 1000 := by
  have hl : 2 ^ 6044 ≤ Nat.lcmUpto 4177 := by decide +kernel
  have hu : Nat.lcmUpto 4177 ≤ 2 ^ (6044 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 4253. -/
private theorem psi_4253_bounds :
    (4264934 : ℝ) / 1000 ≤ Chebyshev.psi 4253 ∧ Chebyshev.psi 4253 ≤ (4265628 : ℝ) / 1000 := by
  have hl : 2 ^ 6153 ≤ Nat.lcmUpto 4253 := by decide +kernel
  have hu : Nat.lcmUpto 4253 ≤ 2 ^ (6153 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- A rational certificate bounds the envelope from 2687 onward. -/
private theorem batch_envelope {t : ℝ} (ht : 2687 ≤ t) :
    (93 : ℝ) ≤
      Real.sqrt t * (Real.log t * (Real.log t - Real.log (Real.log t)) / (8 * Real.pi)) := by
  have h :=
    lee_nosal_envelope_of_log_checks (N := 2687) (lo := 789 / 100) (hi := 79 / 10) (vlo :=
      206 / 100) (vhi := 207 / 100) (c := 93) (j := 12) (k := 4) (n := 32) (m := 32)
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by decide +kernel) (by decide +kernel) (by norm_num only)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact
    h.trans
      (lee_nosal_envelope_mono (x := 2687) (y := t)
        (Real.exp_one_lt_three.le.trans (by norm_num only)) ht)

/-- Every batch cell has a checked psi lower bound. -/
private theorem batch_lower : ∀ r ∈ batchCells, (r.lo : ℝ) / 1000 ≤ Chebyshev.psi r.a := by
  intro r hr
  simp only [batchCells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  · change (2679013 : ℝ) / 1000 ≤ Chebyshev.psi (↑(2687 : ℕ) : ℝ)
    exact psi_2687_bounds.1
  · change (2781599 : ℝ) / 1000 ≤ Chebyshev.psi (↑(2767 : ℕ) : ℝ)
    exact psi_2767_bounds.1
  · change (2864777 : ℝ) / 1000 ≤ Chebyshev.psi (↑(2843 : ℕ) : ℝ)
    exact psi_2843_bounds.1
  · change (2936864 : ℝ) / 1000 ≤ Chebyshev.psi (↑(2917 : ℕ) : ℝ)
    exact psi_2917_bounds.1
  · change (3016576 : ℝ) / 1000 ≤ Chebyshev.psi (↑(3011 : ℕ) : ℝ)
    exact psi_3011_bounds.1
  · change (3105299 : ℝ) / 1000 ≤ Chebyshev.psi (↑(3109 : ℕ) : ℝ)
    exact psi_3109_bounds.1
  · change (3179466 : ℝ) / 1000 ≤ Chebyshev.psi (↑(3198 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 3191) (b := 3198) (by decide) (by decide +kernel)]
    exact psi_3191_bounds.1
  · change (3259871 : ℝ) / 1000 ≤ Chebyshev.psi (↑(3272 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 3271) (b := 3272) (by decide) (by decide +kernel)]
    exact psi_3271_bounds.1
  · change (3340969 : ℝ) / 1000 ≤ Chebyshev.psi (↑(3352 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 3347) (b := 3352) (by decide) (by decide +kernel)]
    exact psi_3347_bounds.1
  · change (3414443 : ℝ) / 1000 ≤ Chebyshev.psi (↑(3433 : ℕ) : ℝ)
    exact psi_3433_bounds.1
  · change (3483757 : ℝ) / 1000 ≤ Chebyshev.psi (↑(3507 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 3499) (b := 3507) (by decide) (by decide +kernel)]
    exact psi_3499_bounds.1
  · change (3573173 : ℝ) / 1000 ≤ Chebyshev.psi (↑(3576 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 3571) (b := 3576) (by decide) (by decide +kernel)]
    exact psi_3571_bounds.1
  · change (3663282 : ℝ) / 1000 ≤ Chebyshev.psi (↑(3666 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 3659) (b := 3666) (by decide) (by decide +kernel)]
    exact psi_3659_bounds.1
  · change (3758244 : ℝ) / 1000 ≤ Chebyshev.psi (↑(3756 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 3739) (b := 3756) (by decide) (by decide +kernel)]
    exact psi_3739_bounds.1
  · change (3849046 : ℝ) / 1000 ≤ Chebyshev.psi (↑(3847 : ℕ) : ℝ)
    exact psi_3847_bounds.1
  · change (3939848 : ℝ) / 1000 ≤ Chebyshev.psi (↑(3923 : ℕ) : ℝ)
    exact psi_3923_bounds.1
  · change (4022333 : ℝ) / 1000 ≤ Chebyshev.psi (↑(4013 : ℕ) : ℝ)
    exact psi_4013_bounds.1
  · change (4105510 : ℝ) / 1000 ≤ Chebyshev.psi (↑(4093 : ℕ) : ℝ)
    exact psi_4093_bounds.1
  · change (4189381 : ℝ) / 1000 ≤ Chebyshev.psi (↑(4177 : ℕ) : ℝ)
    exact psi_4177_bounds.1

/-- Every batch cell has a checked psi upper bound. -/
private theorem batch_upper :
    ∀ r ∈ batchCells, Chebyshev.psi (r.b - 1 : ℕ) ≤ (r.hi : ℝ) / 1000 := by
  intro r hr
  simp only [batchCells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  · change Chebyshev.psi (↑(2766 : ℕ) : ℝ) ≤ (2774669 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 2753) (b := 2766) (by decide) (by decide +kernel)]
    exact psi_2753_bounds.2
  · change Chebyshev.psi (↑(2842 : ℕ) : ℝ) ≤ (2857846 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 2837) (b := 2842) (by decide) (by decide +kernel)]
    exact psi_2837_bounds.2
  · change Chebyshev.psi (↑(2916 : ℕ) : ℝ) ≤ (2929240 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 2909) (b := 2916) (by decide) (by decide +kernel)]
    exact psi_2909_bounds.2
  · change Chebyshev.psi (↑(3010 : ℕ) : ℝ) ≤ (3009646 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 3001) (b := 3010) (by decide) (by decide +kernel)]
    exact psi_3001_bounds.2
  · change Chebyshev.psi (↑(3108 : ℕ) : ℝ) ≤ (3097675 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 3089) (b := 3108) (by decide) (by decide +kernel)]
    exact psi_3089_bounds.2
  · change Chebyshev.psi (↑(3197 : ℕ) : ℝ) ≤ (3180160 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 3191) (b := 3197) (by decide) (by decide +kernel)]
    exact psi_3191_bounds.2
  · change Chebyshev.psi (↑(3271 : ℕ) : ℝ) ≤ (3260565 : ℝ) / 1000
    exact psi_3271_bounds.2
  · change Chebyshev.psi (↑(3351 : ℕ) : ℝ) ≤ (3341663 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 3347) (b := 3351) (by decide) (by decide +kernel)]
    exact psi_3347_bounds.2
  · change Chebyshev.psi (↑(3432 : ℕ) : ℝ) ≤ (3406819 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 3413) (b := 3432) (by decide) (by decide +kernel)]
    exact psi_3413_bounds.2
  · change Chebyshev.psi (↑(3506 : ℕ) : ℝ) ≤ (3484451 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 3499) (b := 3506) (by decide) (by decide +kernel)]
    exact psi_3499_bounds.2
  · change Chebyshev.psi (↑(3575 : ℕ) : ℝ) ≤ (3573867 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 3571) (b := 3575) (by decide) (by decide +kernel)]
    exact psi_3571_bounds.2
  · change Chebyshev.psi (↑(3665 : ℕ) : ℝ) ≤ (3663976 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 3659) (b := 3665) (by decide) (by decide +kernel)]
    exact psi_3659_bounds.2
  · change Chebyshev.psi (↑(3755 : ℕ) : ℝ) ≤ (3758938 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 3739) (b := 3755) (by decide) (by decide +kernel)]
    exact psi_3739_bounds.2
  · change Chebyshev.psi (↑(3846 : ℕ) : ℝ) ≤ (3841422 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 3833) (b := 3846) (by decide) (by decide +kernel)]
    exact psi_3833_bounds.2
  · change Chebyshev.psi (↑(3922 : ℕ) : ℝ) ≤ (3932224 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 3919) (b := 3922) (by decide) (by decide +kernel)]
    exact psi_3919_bounds.2
  · change Chebyshev.psi (↑(4012 : ℕ) : ℝ) ≤ (4014709 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 4007) (b := 4012) (by decide) (by decide +kernel)]
    exact psi_4007_bounds.2
  · change Chebyshev.psi (↑(4092 : ℕ) : ℝ) ≤ (4097887 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 4091) (b := 4092) (by decide) (by decide +kernel)]
    exact psi_4091_bounds.2
  · change Chebyshev.psi (↑(4176 : ℕ) : ℝ) ≤ (4181757 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 4159) (b := 4176) (by decide) (by decide +kernel)]
    exact psi_4159_bounds.2
  · change Chebyshev.psi (↑(4258 : ℕ) : ℝ) ≤ (4265628 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 4253) (b := 4258) (by decide) (by decide +kernel)]
    exact psi_4253_bounds.2

/-- The envelope bound applies at every cell a endpoint. -/
private theorem batch_a :
    ∀ r ∈ batchCells,
      (r.ca : ℝ) / 1000 ≤
        Real.sqrt r.a *
          (Real.log r.a * (Real.log r.a - Real.log (Real.log r.a)) / (8 * Real.pi)) := by
  intro r hr
  simp only [batchCells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  · change
      (93000 : ℝ) / 1000 ≤
        Real.sqrt 2687 *
          (Real.log 2687 * (Real.log 2687 - Real.log (Real.log 2687)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (93000 : ℝ) / 1000 ≤
        Real.sqrt 2767 *
          (Real.log 2767 * (Real.log 2767 - Real.log (Real.log 2767)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (93000 : ℝ) / 1000 ≤
        Real.sqrt 2843 *
          (Real.log 2843 * (Real.log 2843 - Real.log (Real.log 2843)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (93000 : ℝ) / 1000 ≤
        Real.sqrt 2917 *
          (Real.log 2917 * (Real.log 2917 - Real.log (Real.log 2917)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (93000 : ℝ) / 1000 ≤
        Real.sqrt 3011 *
          (Real.log 3011 * (Real.log 3011 - Real.log (Real.log 3011)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (93000 : ℝ) / 1000 ≤
        Real.sqrt 3109 *
          (Real.log 3109 * (Real.log 3109 - Real.log (Real.log 3109)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (93000 : ℝ) / 1000 ≤
        Real.sqrt 3198 *
          (Real.log 3198 * (Real.log 3198 - Real.log (Real.log 3198)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (93000 : ℝ) / 1000 ≤
        Real.sqrt 3272 *
          (Real.log 3272 * (Real.log 3272 - Real.log (Real.log 3272)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (93000 : ℝ) / 1000 ≤
        Real.sqrt 3352 *
          (Real.log 3352 * (Real.log 3352 - Real.log (Real.log 3352)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (93000 : ℝ) / 1000 ≤
        Real.sqrt 3433 *
          (Real.log 3433 * (Real.log 3433 - Real.log (Real.log 3433)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (93000 : ℝ) / 1000 ≤
        Real.sqrt 3507 *
          (Real.log 3507 * (Real.log 3507 - Real.log (Real.log 3507)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (93000 : ℝ) / 1000 ≤
        Real.sqrt 3576 *
          (Real.log 3576 * (Real.log 3576 - Real.log (Real.log 3576)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (93000 : ℝ) / 1000 ≤
        Real.sqrt 3666 *
          (Real.log 3666 * (Real.log 3666 - Real.log (Real.log 3666)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (93000 : ℝ) / 1000 ≤
        Real.sqrt 3756 *
          (Real.log 3756 * (Real.log 3756 - Real.log (Real.log 3756)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (93000 : ℝ) / 1000 ≤
        Real.sqrt 3847 *
          (Real.log 3847 * (Real.log 3847 - Real.log (Real.log 3847)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (93000 : ℝ) / 1000 ≤
        Real.sqrt 3923 *
          (Real.log 3923 * (Real.log 3923 - Real.log (Real.log 3923)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (93000 : ℝ) / 1000 ≤
        Real.sqrt 4013 *
          (Real.log 4013 * (Real.log 4013 - Real.log (Real.log 4013)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (93000 : ℝ) / 1000 ≤
        Real.sqrt 4093 *
          (Real.log 4093 * (Real.log 4093 - Real.log (Real.log 4093)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (93000 : ℝ) / 1000 ≤
        Real.sqrt 4177 *
          (Real.log 4177 * (Real.log 4177 - Real.log (Real.log 4177)) / (8 * Real.pi))
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
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  · change
      (93000 : ℝ) / 1000 ≤
        Real.sqrt 2767 *
          (Real.log 2767 * (Real.log 2767 - Real.log (Real.log 2767)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (93000 : ℝ) / 1000 ≤
        Real.sqrt 2843 *
          (Real.log 2843 * (Real.log 2843 - Real.log (Real.log 2843)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (93000 : ℝ) / 1000 ≤
        Real.sqrt 2917 *
          (Real.log 2917 * (Real.log 2917 - Real.log (Real.log 2917)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (93000 : ℝ) / 1000 ≤
        Real.sqrt 3011 *
          (Real.log 3011 * (Real.log 3011 - Real.log (Real.log 3011)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (93000 : ℝ) / 1000 ≤
        Real.sqrt 3109 *
          (Real.log 3109 * (Real.log 3109 - Real.log (Real.log 3109)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (93000 : ℝ) / 1000 ≤
        Real.sqrt 3198 *
          (Real.log 3198 * (Real.log 3198 - Real.log (Real.log 3198)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (93000 : ℝ) / 1000 ≤
        Real.sqrt 3272 *
          (Real.log 3272 * (Real.log 3272 - Real.log (Real.log 3272)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (93000 : ℝ) / 1000 ≤
        Real.sqrt 3352 *
          (Real.log 3352 * (Real.log 3352 - Real.log (Real.log 3352)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (93000 : ℝ) / 1000 ≤
        Real.sqrt 3433 *
          (Real.log 3433 * (Real.log 3433 - Real.log (Real.log 3433)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (93000 : ℝ) / 1000 ≤
        Real.sqrt 3507 *
          (Real.log 3507 * (Real.log 3507 - Real.log (Real.log 3507)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (93000 : ℝ) / 1000 ≤
        Real.sqrt 3576 *
          (Real.log 3576 * (Real.log 3576 - Real.log (Real.log 3576)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (93000 : ℝ) / 1000 ≤
        Real.sqrt 3666 *
          (Real.log 3666 * (Real.log 3666 - Real.log (Real.log 3666)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (93000 : ℝ) / 1000 ≤
        Real.sqrt 3756 *
          (Real.log 3756 * (Real.log 3756 - Real.log (Real.log 3756)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (93000 : ℝ) / 1000 ≤
        Real.sqrt 3847 *
          (Real.log 3847 * (Real.log 3847 - Real.log (Real.log 3847)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (93000 : ℝ) / 1000 ≤
        Real.sqrt 3923 *
          (Real.log 3923 * (Real.log 3923 - Real.log (Real.log 3923)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (93000 : ℝ) / 1000 ≤
        Real.sqrt 4013 *
          (Real.log 4013 * (Real.log 4013 - Real.log (Real.log 4013)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (93000 : ℝ) / 1000 ≤
        Real.sqrt 4093 *
          (Real.log 4093 * (Real.log 4093 - Real.log (Real.log 4093)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (93000 : ℝ) / 1000 ≤
        Real.sqrt 4177 *
          (Real.log 4177 * (Real.log 4177 - Real.log (Real.log 4177)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (93000 : ℝ) / 1000 ≤
        Real.sqrt 4259 *
          (Real.log 4259 * (Real.log 4259 - Real.log (Real.log 4259)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)

/-- The checked batch proves the Lee–Nosal psi estimate on `[2687, 4259)`. -/
theorem psi_lee_nosal_2687_4259 {x : ℝ} (ha : 2687 ≤ x) (hb : x < 4259) :
    |Chebyshev.psi x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  exact
    lee_nosal_chain_sound Chebyshev.psi_mono Chebyshev.psi_eq_psi_coe_floor (by decide +kernel)
      batch_lower batch_upper batch_a batch_b ha hb

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
