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
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevDefect3600
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalLogCheck
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalMonotone
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalChecker

/-! # Batch certificate for Lee–Nosal theta cells -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The local cells store endpoint bounds in thousandths. -/
private def batchCells : List LeeNosalCell :=
  [⟨2900, 2920, 2821584, 2937558, 99000, 99000⟩, ⟨2920, 2944, 2845844, 2953501, 99000, 99000⟩,
    ⟨2944, 2960, 2861786, 2969443, 99000, 99000⟩, ⟨2960, 2976, 2877729, 2993703, 99000, 99000⟩,
    ⟨2976, 3000, 2901989, 3001328, 99000, 99000⟩, ⟨3000, 3008, 2909614, 3009646, 99000, 99000⟩,
    ⟨3008, 3016, 2917931, 3017270, 99000, 99000⟩, ⟨3016, 3024, 2925556, 3033213, 99000, 99000⟩,
    ⟨3024, 3040, 2941498, 3041530, 99000, 99000⟩, ⟨3040, 3048, 2949816, 3049848, 99000, 99000⟩,
    ⟨3048, 3057, 2958134, 3057473, 99000, 99000⟩, ⟨3057, 3064, 2965759, 3065790, 99000, 99000⟩,
    ⟨3064, 3073, 2974076, 3073415, 99000, 99000⟩, ⟨3073, 3080, 2981701, 3081733, 99000, 99000⟩,
    ⟨3080, 3089, 2990019, 3089357, 99000, 99000⟩, ⟨3089, 3104, 3005961, 3097675, 99000, 99000⟩]

/-- The kernel-checked prefix bounds for 2897. -/
private theorem psi_2897_bounds :
    (2912604 : ℝ) / 1000 ≤ Chebyshev.psi 2897 ∧ Chebyshev.psi 2897 ≤ (2913298 : ℝ) / 1000 := by
  have hl : 2 ^ 4202 ≤ Nat.lcmUpto 2897 := by decide +kernel
  have hu : Nat.lcmUpto 2897 ≤ 2 ^ (4202 + 1) := by decide +kernel
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

/-- The kernel-checked prefix bounds for 2939. -/
private theorem psi_2939_bounds :
    (2952806 : ℝ) / 1000 ≤ Chebyshev.psi 2939 ∧ Chebyshev.psi 2939 ≤ (2953501 : ℝ) / 1000 := by
  have hl : 2 ^ 4260 ≤ Nat.lcmUpto 2939 := by decide +kernel
  have hu : Nat.lcmUpto 2939 ≤ 2 ^ (4260 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 2957. -/
private theorem psi_2957_bounds :
    (2968749 : ℝ) / 1000 ≤ Chebyshev.psi 2957 ∧ Chebyshev.psi 2957 ≤ (2969443 : ℝ) / 1000 := by
  have hl : 2 ^ 4283 ≤ Nat.lcmUpto 2957 := by decide +kernel
  have hu : Nat.lcmUpto 2957 ≤ 2 ^ (4283 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 2971. -/
private theorem psi_2971_bounds :
    (2993009 : ℝ) / 1000 ≤ Chebyshev.psi 2971 ∧ Chebyshev.psi 2971 ≤ (2993703 : ℝ) / 1000 := by
  have hl : 2 ^ 4318 ≤ Nat.lcmUpto 2971 := by decide +kernel
  have hu : Nat.lcmUpto 2971 ≤ 2 ^ (4318 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 2999. -/
private theorem psi_2999_bounds :
    (3000634 : ℝ) / 1000 ≤ Chebyshev.psi 2999 ∧ Chebyshev.psi 2999 ≤ (3001328 : ℝ) / 1000 := by
  have hl : 2 ^ 4329 ≤ Nat.lcmUpto 2999 := by decide +kernel
  have hu : Nat.lcmUpto 2999 ≤ 2 ^ (4329 + 1) := by decide +kernel
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

/-- The kernel-checked prefix bounds for 3023. -/
private theorem psi_3023_bounds :
    (3032518 : ℝ) / 1000 ≤ Chebyshev.psi 3023 ∧ Chebyshev.psi 3023 ≤ (3033213 : ℝ) / 1000 := by
  have hl : 2 ^ 4375 ≤ Nat.lcmUpto 3023 := by decide +kernel
  have hu : Nat.lcmUpto 3023 ≤ 2 ^ (4375 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 3037. -/
private theorem psi_3037_bounds :
    (3040836 : ℝ) / 1000 ≤ Chebyshev.psi 3037 ∧ Chebyshev.psi 3037 ≤ (3041530 : ℝ) / 1000 := by
  have hl : 2 ^ 4387 ≤ Nat.lcmUpto 3037 := by decide +kernel
  have hu : Nat.lcmUpto 3037 ≤ 2 ^ (4387 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 3041. -/
private theorem psi_3041_bounds :
    (3049154 : ℝ) / 1000 ≤ Chebyshev.psi 3041 ∧ Chebyshev.psi 3041 ≤ (3049848 : ℝ) / 1000 := by
  have hl : 2 ^ 4399 ≤ Nat.lcmUpto 3041 := by decide +kernel
  have hu : Nat.lcmUpto 3041 ≤ 2 ^ (4399 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 3049. -/
private theorem psi_3049_bounds :
    (3056779 : ℝ) / 1000 ≤ Chebyshev.psi 3049 ∧ Chebyshev.psi 3049 ≤ (3057473 : ℝ) / 1000 := by
  have hl : 2 ^ 4410 ≤ Nat.lcmUpto 3049 := by decide +kernel
  have hu : Nat.lcmUpto 3049 ≤ 2 ^ (4410 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 3061. -/
private theorem psi_3061_bounds :
    (3065096 : ℝ) / 1000 ≤ Chebyshev.psi 3061 ∧ Chebyshev.psi 3061 ≤ (3065790 : ℝ) / 1000 := by
  have hl : 2 ^ 4422 ≤ Nat.lcmUpto 3061 := by decide +kernel
  have hu : Nat.lcmUpto 3061 ≤ 2 ^ (4422 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 3067. -/
private theorem psi_3067_bounds :
    (3072721 : ℝ) / 1000 ≤ Chebyshev.psi 3067 ∧ Chebyshev.psi 3067 ≤ (3073415 : ℝ) / 1000 := by
  have hl : 2 ^ 4433 ≤ Nat.lcmUpto 3067 := by decide +kernel
  have hu : Nat.lcmUpto 3067 ≤ 2 ^ (4433 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 3079. -/
private theorem psi_3079_bounds :
    (3081039 : ℝ) / 1000 ≤ Chebyshev.psi 3079 ∧ Chebyshev.psi 3079 ≤ (3081733 : ℝ) / 1000 := by
  have hl : 2 ^ 4445 ≤ Nat.lcmUpto 3079 := by decide +kernel
  have hu : Nat.lcmUpto 3079 ≤ 2 ^ (4445 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 3083. -/
private theorem psi_3083_bounds :
    (3088663 : ℝ) / 1000 ≤ Chebyshev.psi 3083 ∧ Chebyshev.psi 3083 ≤ (3089357 : ℝ) / 1000 := by
  have hl : 2 ^ 4456 ≤ Nat.lcmUpto 3083 := by decide +kernel
  have hu : Nat.lcmUpto 3083 ≤ 2 ^ (4456 + 1) := by decide +kernel
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

/-- A rational certificate bounds the envelope from 2900 onward. -/
private theorem batch_envelope {t : ℝ} (ht : 2900 ≤ t) :
    (99 : ℝ) ≤
      Real.sqrt t * (Real.log t * (Real.log t - Real.log (Real.log t)) / (8 * Real.pi)) := by
  have h :=
    lee_nosal_envelope_of_log_checks (N := 2900) (lo := 797 / 100) (hi := 798 / 100) (vlo :=
      207 / 100) (vhi := 208 / 100) (c := 99) (j := 12) (k := 4) (n := 32) (m := 32)
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by decide +kernel) (by decide +kernel) (by norm_num only)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact
    h.trans
      (lee_nosal_envelope_mono (x := 2900) (y := t)
        (Real.exp_one_lt_three.le.trans (by norm_num only)) ht)

/-- Every batch cell has a checked theta lower bound. -/
private theorem batch_lower : ∀ r ∈ batchCells, (r.lo : ℝ) / 1000 ≤ Chebyshev.theta r.a := by
  intro r hr
  simp only [batchCells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · change (2821584 : ℝ) / 1000 ≤ Chebyshev.theta (↑(2900 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_9102 (x := 2900) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 2897) (b := 2900) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_2897_bounds.1]
  · change (2845844 : ℝ) / 1000 ≤ Chebyshev.theta (↑(2920 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_9102 (x := 2920) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 2917) (b := 2920) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_2917_bounds.1]
  · change (2861786 : ℝ) / 1000 ≤ Chebyshev.theta (↑(2944 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_9102 (x := 2944) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 2939) (b := 2944) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_2939_bounds.1]
  · change (2877729 : ℝ) / 1000 ≤ Chebyshev.theta (↑(2960 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_9102 (x := 2960) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 2957) (b := 2960) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_2957_bounds.1]
  · change (2901989 : ℝ) / 1000 ≤ Chebyshev.theta (↑(2976 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_9102 (x := 2976) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 2971) (b := 2976) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_2971_bounds.1]
  · change (2909614 : ℝ) / 1000 ≤ Chebyshev.theta (↑(3000 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_9102 (x := 3000) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 2999) (b := 3000) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_2999_bounds.1]
  · change (2917931 : ℝ) / 1000 ≤ Chebyshev.theta (↑(3008 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_9102 (x := 3008) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3001) (b := 3008) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3001_bounds.1]
  · change (2925556 : ℝ) / 1000 ≤ Chebyshev.theta (↑(3016 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_9102 (x := 3016) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3011) (b := 3016) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3011_bounds.1]
  · change (2941498 : ℝ) / 1000 ≤ Chebyshev.theta (↑(3024 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_9102 (x := 3024) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3023) (b := 3024) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3023_bounds.1]
  · change (2949816 : ℝ) / 1000 ≤ Chebyshev.theta (↑(3040 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_9102 (x := 3040) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3037) (b := 3040) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3037_bounds.1]
  · change (2958134 : ℝ) / 1000 ≤ Chebyshev.theta (↑(3048 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_9102 (x := 3048) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3041) (b := 3048) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3041_bounds.1]
  · change (2965759 : ℝ) / 1000 ≤ Chebyshev.theta (↑(3057 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_9102 (x := 3057) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3049) (b := 3057) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3049_bounds.1]
  · change (2974076 : ℝ) / 1000 ≤ Chebyshev.theta (↑(3064 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_9102 (x := 3064) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3061) (b := 3064) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3061_bounds.1]
  · change (2981701 : ℝ) / 1000 ≤ Chebyshev.theta (↑(3073 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_9102 (x := 3073) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3067) (b := 3073) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3067_bounds.1]
  · change (2990019 : ℝ) / 1000 ≤ Chebyshev.theta (↑(3080 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_9102 (x := 3080) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3079) (b := 3080) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3079_bounds.1]
  · change (3005961 : ℝ) / 1000 ≤ Chebyshev.theta (↑(3089 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_9102 (x := 3089) (by norm_num only) (by norm_num only)
    linarith only [hd, psi_3089_bounds.1]

/-- Every batch cell has a checked theta upper bound. -/
private theorem batch_upper :
    ∀ r ∈ batchCells, Chebyshev.theta (r.b - 1 : ℕ) ≤ (r.hi : ℝ) / 1000 := by
  intro r hr
  simp only [batchCells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · change Chebyshev.theta (↑(2919 : ℕ) : ℝ) ≤ (2937558 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 2919
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 2917) (b := 2919) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_2917_bounds.2]
  · change Chebyshev.theta (↑(2943 : ℕ) : ℝ) ≤ (2953501 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 2943
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 2939) (b := 2943) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_2939_bounds.2]
  · change Chebyshev.theta (↑(2959 : ℕ) : ℝ) ≤ (2969443 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 2959
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 2957) (b := 2959) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_2957_bounds.2]
  · change Chebyshev.theta (↑(2975 : ℕ) : ℝ) ≤ (2993703 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 2975
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 2971) (b := 2975) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_2971_bounds.2]
  · change Chebyshev.theta (↑(2999 : ℕ) : ℝ) ≤ (3001328 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 2999
    linarith only [hd, psi_2999_bounds.2]
  · change Chebyshev.theta (↑(3007 : ℕ) : ℝ) ≤ (3009646 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 3007
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3001) (b := 3007) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3001_bounds.2]
  · change Chebyshev.theta (↑(3015 : ℕ) : ℝ) ≤ (3017270 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 3015
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3011) (b := 3015) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3011_bounds.2]
  · change Chebyshev.theta (↑(3023 : ℕ) : ℝ) ≤ (3033213 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 3023
    linarith only [hd, psi_3023_bounds.2]
  · change Chebyshev.theta (↑(3039 : ℕ) : ℝ) ≤ (3041530 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 3039
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3037) (b := 3039) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3037_bounds.2]
  · change Chebyshev.theta (↑(3047 : ℕ) : ℝ) ≤ (3049848 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 3047
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3041) (b := 3047) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3041_bounds.2]
  · change Chebyshev.theta (↑(3056 : ℕ) : ℝ) ≤ (3057473 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 3056
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3049) (b := 3056) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3049_bounds.2]
  · change Chebyshev.theta (↑(3063 : ℕ) : ℝ) ≤ (3065790 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 3063
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3061) (b := 3063) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3061_bounds.2]
  · change Chebyshev.theta (↑(3072 : ℕ) : ℝ) ≤ (3073415 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 3072
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3067) (b := 3072) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3067_bounds.2]
  · change Chebyshev.theta (↑(3079 : ℕ) : ℝ) ≤ (3081733 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 3079
    linarith only [hd, psi_3079_bounds.2]
  · change Chebyshev.theta (↑(3088 : ℕ) : ℝ) ≤ (3089357 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 3088
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3083) (b := 3088) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3083_bounds.2]
  · change Chebyshev.theta (↑(3103 : ℕ) : ℝ) ≤ (3097675 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 3103
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3089) (b := 3103) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3089_bounds.2]

/-- The envelope bound applies at every cell a endpoint. -/
private theorem batch_a :
    ∀ r ∈ batchCells,
      (r.ca : ℝ) / 1000 ≤
        Real.sqrt r.a *
          (Real.log r.a * (Real.log r.a - Real.log (Real.log r.a)) / (8 * Real.pi)) := by
  intro r hr
  simp only [batchCells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · change
      (99000 : ℝ) / 1000 ≤
        Real.sqrt 2900 *
          (Real.log 2900 * (Real.log 2900 - Real.log (Real.log 2900)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (99000 : ℝ) / 1000 ≤
        Real.sqrt 2920 *
          (Real.log 2920 * (Real.log 2920 - Real.log (Real.log 2920)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (99000 : ℝ) / 1000 ≤
        Real.sqrt 2944 *
          (Real.log 2944 * (Real.log 2944 - Real.log (Real.log 2944)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (99000 : ℝ) / 1000 ≤
        Real.sqrt 2960 *
          (Real.log 2960 * (Real.log 2960 - Real.log (Real.log 2960)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (99000 : ℝ) / 1000 ≤
        Real.sqrt 2976 *
          (Real.log 2976 * (Real.log 2976 - Real.log (Real.log 2976)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (99000 : ℝ) / 1000 ≤
        Real.sqrt 3000 *
          (Real.log 3000 * (Real.log 3000 - Real.log (Real.log 3000)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (99000 : ℝ) / 1000 ≤
        Real.sqrt 3008 *
          (Real.log 3008 * (Real.log 3008 - Real.log (Real.log 3008)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (99000 : ℝ) / 1000 ≤
        Real.sqrt 3016 *
          (Real.log 3016 * (Real.log 3016 - Real.log (Real.log 3016)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (99000 : ℝ) / 1000 ≤
        Real.sqrt 3024 *
          (Real.log 3024 * (Real.log 3024 - Real.log (Real.log 3024)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (99000 : ℝ) / 1000 ≤
        Real.sqrt 3040 *
          (Real.log 3040 * (Real.log 3040 - Real.log (Real.log 3040)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (99000 : ℝ) / 1000 ≤
        Real.sqrt 3048 *
          (Real.log 3048 * (Real.log 3048 - Real.log (Real.log 3048)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (99000 : ℝ) / 1000 ≤
        Real.sqrt 3057 *
          (Real.log 3057 * (Real.log 3057 - Real.log (Real.log 3057)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (99000 : ℝ) / 1000 ≤
        Real.sqrt 3064 *
          (Real.log 3064 * (Real.log 3064 - Real.log (Real.log 3064)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (99000 : ℝ) / 1000 ≤
        Real.sqrt 3073 *
          (Real.log 3073 * (Real.log 3073 - Real.log (Real.log 3073)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (99000 : ℝ) / 1000 ≤
        Real.sqrt 3080 *
          (Real.log 3080 * (Real.log 3080 - Real.log (Real.log 3080)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (99000 : ℝ) / 1000 ≤
        Real.sqrt 3089 *
          (Real.log 3089 * (Real.log 3089 - Real.log (Real.log 3089)) / (8 * Real.pi))
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
    rfl | rfl
  · change
      (99000 : ℝ) / 1000 ≤
        Real.sqrt 2920 *
          (Real.log 2920 * (Real.log 2920 - Real.log (Real.log 2920)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (99000 : ℝ) / 1000 ≤
        Real.sqrt 2944 *
          (Real.log 2944 * (Real.log 2944 - Real.log (Real.log 2944)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (99000 : ℝ) / 1000 ≤
        Real.sqrt 2960 *
          (Real.log 2960 * (Real.log 2960 - Real.log (Real.log 2960)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (99000 : ℝ) / 1000 ≤
        Real.sqrt 2976 *
          (Real.log 2976 * (Real.log 2976 - Real.log (Real.log 2976)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (99000 : ℝ) / 1000 ≤
        Real.sqrt 3000 *
          (Real.log 3000 * (Real.log 3000 - Real.log (Real.log 3000)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (99000 : ℝ) / 1000 ≤
        Real.sqrt 3008 *
          (Real.log 3008 * (Real.log 3008 - Real.log (Real.log 3008)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (99000 : ℝ) / 1000 ≤
        Real.sqrt 3016 *
          (Real.log 3016 * (Real.log 3016 - Real.log (Real.log 3016)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (99000 : ℝ) / 1000 ≤
        Real.sqrt 3024 *
          (Real.log 3024 * (Real.log 3024 - Real.log (Real.log 3024)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (99000 : ℝ) / 1000 ≤
        Real.sqrt 3040 *
          (Real.log 3040 * (Real.log 3040 - Real.log (Real.log 3040)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (99000 : ℝ) / 1000 ≤
        Real.sqrt 3048 *
          (Real.log 3048 * (Real.log 3048 - Real.log (Real.log 3048)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (99000 : ℝ) / 1000 ≤
        Real.sqrt 3057 *
          (Real.log 3057 * (Real.log 3057 - Real.log (Real.log 3057)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (99000 : ℝ) / 1000 ≤
        Real.sqrt 3064 *
          (Real.log 3064 * (Real.log 3064 - Real.log (Real.log 3064)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (99000 : ℝ) / 1000 ≤
        Real.sqrt 3073 *
          (Real.log 3073 * (Real.log 3073 - Real.log (Real.log 3073)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (99000 : ℝ) / 1000 ≤
        Real.sqrt 3080 *
          (Real.log 3080 * (Real.log 3080 - Real.log (Real.log 3080)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (99000 : ℝ) / 1000 ≤
        Real.sqrt 3089 *
          (Real.log 3089 * (Real.log 3089 - Real.log (Real.log 3089)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (99000 : ℝ) / 1000 ≤
        Real.sqrt 3104 *
          (Real.log 3104 * (Real.log 3104 - Real.log (Real.log 3104)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)

/-- The checked batch proves the Lee–Nosal theta estimate on `[2900, 3104)`. -/
theorem theta_lee_nosal_2900_3104 {x : ℝ} (ha : 2900 ≤ x) (hb : x < 3104) :
    |Chebyshev.theta x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  exact
    lee_nosal_chain_sound Chebyshev.theta_mono Chebyshev.theta_eq_theta_coe_floor
      (by decide +kernel) batch_lower batch_upper batch_a batch_b ha hb

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
