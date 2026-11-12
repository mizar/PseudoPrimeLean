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
  [⟨3160, 3163, 3055705, 3131639, 107500, 107500⟩, ⟨3163, 3170, 3063330, 3155900, 107500, 107500⟩,
    ⟨3170, 3187, 3079965, 3163524, 107500, 107500⟩, ⟨3187, 3203, 3095908, 3180160, 107500, 107500⟩,
    ⟨3203, 3219, 3111850, 3204420, 107500, 107500⟩, ⟨3219, 3235, 3128486, 3220362, 107500, 107500⟩,
    ⟨3235, 3251, 3144428, 3220362, 107500, 107500⟩, ⟨3251, 3260, 3152746, 3252940, 107500, 107500⟩,
    ⟨3260, 3284, 3177006, 3260565, 107500, 107500⟩, ⟨3284, 3292, 3184631, 3260565, 107500, 107500⟩]

/-- The kernel-checked prefix bounds for 3137. -/
private theorem psi_3137_bounds :
    (3130945 : ℝ) / 1000 ≤ Chebyshev.psi 3137 ∧ Chebyshev.psi 3137 ≤ (3131639 : ℝ) / 1000 := by
  have hl : 2 ^ 4517 ≤ Nat.lcmUpto 3137 := by decide +kernel
  have hu : Nat.lcmUpto 3137 ≤ 2 ^ (4517 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 3163. -/
private theorem psi_3163_bounds :
    (3138570 : ℝ) / 1000 ≤ Chebyshev.psi 3163 ∧ Chebyshev.psi 3163 ≤ (3139264 : ℝ) / 1000 := by
  have hl : 2 ^ 4528 ≤ Nat.lcmUpto 3163 := by decide +kernel
  have hu : Nat.lcmUpto 3163 ≤ 2 ^ (4528 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 3169. -/
private theorem psi_3169_bounds :
    (3155205 : ℝ) / 1000 ≤ Chebyshev.psi 3169 ∧ Chebyshev.psi 3169 ≤ (3155900 : ℝ) / 1000 := by
  have hl : 2 ^ 4552 ≤ Nat.lcmUpto 3169 := by decide +kernel
  have hu : Nat.lcmUpto 3169 ≤ 2 ^ (4552 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 3181. -/
private theorem psi_3181_bounds :
    (3162830 : ℝ) / 1000 ≤ Chebyshev.psi 3181 ∧ Chebyshev.psi 3181 ≤ (3163524 : ℝ) / 1000 := by
  have hl : 2 ^ 4563 ≤ Nat.lcmUpto 3181 := by decide +kernel
  have hu : Nat.lcmUpto 3181 ≤ 2 ^ (4563 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 3187. -/
private theorem psi_3187_bounds :
    (3171148 : ℝ) / 1000 ≤ Chebyshev.psi 3187 ∧ Chebyshev.psi 3187 ≤ (3171842 : ℝ) / 1000 := by
  have hl : 2 ^ 4575 ≤ Nat.lcmUpto 3187 := by decide +kernel
  have hu : Nat.lcmUpto 3187 ≤ 2 ^ (4575 + 1) := by decide +kernel
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

/-- The kernel-checked prefix bounds for 3203. -/
private theorem psi_3203_bounds :
    (3187090 : ℝ) / 1000 ≤ Chebyshev.psi 3203 ∧ Chebyshev.psi 3203 ≤ (3187784 : ℝ) / 1000 := by
  have hl : 2 ^ 4598 ≤ Nat.lcmUpto 3203 := by decide +kernel
  have hu : Nat.lcmUpto 3203 ≤ 2 ^ (4598 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 3217. -/
private theorem psi_3217_bounds :
    (3203726 : ℝ) / 1000 ≤ Chebyshev.psi 3217 ∧ Chebyshev.psi 3217 ≤ (3204420 : ℝ) / 1000 := by
  have hl : 2 ^ 4622 ≤ Nat.lcmUpto 3217 := by decide +kernel
  have hu : Nat.lcmUpto 3217 ≤ 2 ^ (4622 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 3229. -/
private theorem psi_3229_bounds :
    (3219668 : ℝ) / 1000 ≤ Chebyshev.psi 3229 ∧ Chebyshev.psi 3229 ≤ (3220362 : ℝ) / 1000 := by
  have hl : 2 ^ 4645 ≤ Nat.lcmUpto 3229 := by decide +kernel
  have hu : Nat.lcmUpto 3229 ≤ 2 ^ (4645 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 3251. -/
private theorem psi_3251_bounds :
    (3227986 : ℝ) / 1000 ≤ Chebyshev.psi 3251 ∧ Chebyshev.psi 3251 ≤ (3228680 : ℝ) / 1000 := by
  have hl : 2 ^ 4657 ≤ Nat.lcmUpto 3251 := by decide +kernel
  have hu : Nat.lcmUpto 3251 ≤ 2 ^ (4657 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 3259. -/
private theorem psi_3259_bounds :
    (3252246 : ℝ) / 1000 ≤ Chebyshev.psi 3259 ∧ Chebyshev.psi 3259 ≤ (3252940 : ℝ) / 1000 := by
  have hl : 2 ^ 4692 ≤ Nat.lcmUpto 3259 := by decide +kernel
  have hu : Nat.lcmUpto 3259 ≤ 2 ^ (4692 + 1) := by decide +kernel
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

/-- A rational certificate bounds the envelope from 3160 onward. -/
private theorem batch_envelope {t : ℝ} (ht : 3160 ≤ t) :
    (215 / 2 : ℝ) ≤
      Real.sqrt t * (Real.log t * (Real.log t - Real.log (Real.log t)) / (8 * Real.pi)) := by
  have h :=
    lee_nosal_envelope_of_log_checks (N := 3160) (lo := 8058 / 1000) (hi := 8059 / 1000) (vlo :=
      2086 / 1000) (vhi := 2087 / 1000) (c := 215 / 2) (j := 12) (k := 4) (n := 32) (m := 32)
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by decide +kernel) (by decide +kernel) (by norm_num only)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact
    h.trans
      (lee_nosal_envelope_mono (x := 3160) (y := t)
        (Real.exp_one_lt_three.le.trans (by norm_num only)) ht)

/-- Every batch cell has a checked theta lower bound. -/
private theorem batch_lower : ∀ r ∈ batchCells, (r.lo : ℝ) / 1000 ≤ Chebyshev.theta r.a := by
  intro r hr
  simp only [batchCells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change (3055705 : ℝ) / 1000 ≤ Chebyshev.theta (↑(3160 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_7524 (x := 3160) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3137) (b := 3160) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3137_bounds.1]
  · change (3063330 : ℝ) / 1000 ≤ Chebyshev.theta (↑(3163 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_7524 (x := 3163) (by norm_num only) (by norm_num only)
    linarith only [hd, psi_3163_bounds.1]
  · change (3079965 : ℝ) / 1000 ≤ Chebyshev.theta (↑(3170 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_7524 (x := 3170) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3169) (b := 3170) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3169_bounds.1]
  · change (3095908 : ℝ) / 1000 ≤ Chebyshev.theta (↑(3187 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_7524 (x := 3187) (by norm_num only) (by norm_num only)
    linarith only [hd, psi_3187_bounds.1]
  · change (3111850 : ℝ) / 1000 ≤ Chebyshev.theta (↑(3203 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_7524 (x := 3203) (by norm_num only) (by norm_num only)
    linarith only [hd, psi_3203_bounds.1]
  · change (3128486 : ℝ) / 1000 ≤ Chebyshev.theta (↑(3219 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_7524 (x := 3219) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3217) (b := 3219) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3217_bounds.1]
  · change (3144428 : ℝ) / 1000 ≤ Chebyshev.theta (↑(3235 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_7524 (x := 3235) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3229) (b := 3235) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3229_bounds.1]
  · change (3152746 : ℝ) / 1000 ≤ Chebyshev.theta (↑(3251 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_7524 (x := 3251) (by norm_num only) (by norm_num only)
    linarith only [hd, psi_3251_bounds.1]
  · change (3177006 : ℝ) / 1000 ≤ Chebyshev.theta (↑(3260 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_7524 (x := 3260) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3259) (b := 3260) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3259_bounds.1]
  · change (3184631 : ℝ) / 1000 ≤ Chebyshev.theta (↑(3284 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_7524 (x := 3284) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3271) (b := 3284) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3271_bounds.1]

/-- Every batch cell has a checked theta upper bound. -/
private theorem batch_upper :
    ∀ r ∈ batchCells, Chebyshev.theta (r.b - 1 : ℕ) ≤ (r.hi : ℝ) / 1000 := by
  intro r hr
  simp only [batchCells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change Chebyshev.theta (↑(3162 : ℕ) : ℝ) ≤ (3131639 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 3162
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3137) (b := 3162) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3137_bounds.2]
  · change Chebyshev.theta (↑(3169 : ℕ) : ℝ) ≤ (3155900 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 3169
    linarith only [hd, psi_3169_bounds.2]
  · change Chebyshev.theta (↑(3186 : ℕ) : ℝ) ≤ (3163524 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 3186
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3181) (b := 3186) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3181_bounds.2]
  · change Chebyshev.theta (↑(3202 : ℕ) : ℝ) ≤ (3180160 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 3202
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3191) (b := 3202) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3191_bounds.2]
  · change Chebyshev.theta (↑(3218 : ℕ) : ℝ) ≤ (3204420 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 3218
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3217) (b := 3218) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3217_bounds.2]
  · change Chebyshev.theta (↑(3234 : ℕ) : ℝ) ≤ (3220362 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 3234
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3229) (b := 3234) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3229_bounds.2]
  · change Chebyshev.theta (↑(3250 : ℕ) : ℝ) ≤ (3220362 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 3250
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3229) (b := 3250) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3229_bounds.2]
  · change Chebyshev.theta (↑(3259 : ℕ) : ℝ) ≤ (3252940 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 3259
    linarith only [hd, psi_3259_bounds.2]
  · change Chebyshev.theta (↑(3283 : ℕ) : ℝ) ≤ (3260565 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 3283
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3271) (b := 3283) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3271_bounds.2]
  · change Chebyshev.theta (↑(3291 : ℕ) : ℝ) ≤ (3260565 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 3291
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3271) (b := 3291) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3271_bounds.2]

/-- The envelope bound applies at every cell a endpoint. -/
private theorem batch_a :
    ∀ r ∈ batchCells,
      (r.ca : ℝ) / 1000 ≤
        Real.sqrt r.a *
          (Real.log r.a * (Real.log r.a - Real.log (Real.log r.a)) / (8 * Real.pi)) := by
  intro r hr
  simp only [batchCells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change
      (107500 : ℝ) / 1000 ≤
        Real.sqrt 3160 *
          (Real.log 3160 * (Real.log 3160 - Real.log (Real.log 3160)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (107500 : ℝ) / 1000 ≤
        Real.sqrt 3163 *
          (Real.log 3163 * (Real.log 3163 - Real.log (Real.log 3163)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (107500 : ℝ) / 1000 ≤
        Real.sqrt 3170 *
          (Real.log 3170 * (Real.log 3170 - Real.log (Real.log 3170)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (107500 : ℝ) / 1000 ≤
        Real.sqrt 3187 *
          (Real.log 3187 * (Real.log 3187 - Real.log (Real.log 3187)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (107500 : ℝ) / 1000 ≤
        Real.sqrt 3203 *
          (Real.log 3203 * (Real.log 3203 - Real.log (Real.log 3203)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (107500 : ℝ) / 1000 ≤
        Real.sqrt 3219 *
          (Real.log 3219 * (Real.log 3219 - Real.log (Real.log 3219)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (107500 : ℝ) / 1000 ≤
        Real.sqrt 3235 *
          (Real.log 3235 * (Real.log 3235 - Real.log (Real.log 3235)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (107500 : ℝ) / 1000 ≤
        Real.sqrt 3251 *
          (Real.log 3251 * (Real.log 3251 - Real.log (Real.log 3251)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (107500 : ℝ) / 1000 ≤
        Real.sqrt 3260 *
          (Real.log 3260 * (Real.log 3260 - Real.log (Real.log 3260)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (107500 : ℝ) / 1000 ≤
        Real.sqrt 3284 *
          (Real.log 3284 * (Real.log 3284 - Real.log (Real.log 3284)) / (8 * Real.pi))
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
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change
      (107500 : ℝ) / 1000 ≤
        Real.sqrt 3163 *
          (Real.log 3163 * (Real.log 3163 - Real.log (Real.log 3163)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (107500 : ℝ) / 1000 ≤
        Real.sqrt 3170 *
          (Real.log 3170 * (Real.log 3170 - Real.log (Real.log 3170)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (107500 : ℝ) / 1000 ≤
        Real.sqrt 3187 *
          (Real.log 3187 * (Real.log 3187 - Real.log (Real.log 3187)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (107500 : ℝ) / 1000 ≤
        Real.sqrt 3203 *
          (Real.log 3203 * (Real.log 3203 - Real.log (Real.log 3203)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (107500 : ℝ) / 1000 ≤
        Real.sqrt 3219 *
          (Real.log 3219 * (Real.log 3219 - Real.log (Real.log 3219)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (107500 : ℝ) / 1000 ≤
        Real.sqrt 3235 *
          (Real.log 3235 * (Real.log 3235 - Real.log (Real.log 3235)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (107500 : ℝ) / 1000 ≤
        Real.sqrt 3251 *
          (Real.log 3251 * (Real.log 3251 - Real.log (Real.log 3251)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (107500 : ℝ) / 1000 ≤
        Real.sqrt 3260 *
          (Real.log 3260 * (Real.log 3260 - Real.log (Real.log 3260)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (107500 : ℝ) / 1000 ≤
        Real.sqrt 3284 *
          (Real.log 3284 * (Real.log 3284 - Real.log (Real.log 3284)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (107500 : ℝ) / 1000 ≤
        Real.sqrt 3292 *
          (Real.log 3292 * (Real.log 3292 - Real.log (Real.log 3292)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)

/-- The checked batch proves the Lee–Nosal theta estimate on `[3160, 3292)`. -/
theorem theta_lee_nosal_3160_3292 {x : ℝ} (ha : 3160 ≤ x) (hb : x < 3292) :
    |Chebyshev.theta x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  exact
    lee_nosal_chain_sound Chebyshev.theta_mono Chebyshev.theta_eq_theta_coe_floor
      (by decide +kernel) batch_lower batch_upper batch_a batch_b ha hb

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
