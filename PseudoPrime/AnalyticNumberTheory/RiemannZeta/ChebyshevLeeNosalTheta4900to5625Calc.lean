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
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSmallDefect5625
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalLogCheck
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalMonotone
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalChecker

/-! # Batch certificate for Lee–Nosal theta cells -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The local cells store endpoint bounds in thousandths. -/
def theta4900Cells : List LeeNosalCell :=
  [⟨4900, 4919, 4770919, 4887381, 149000, 149000⟩, ⟨4919, 4948, 4799338, 4930356, 149000, 149000⟩,
    ⟨4948, 4982, 4833302, 4972638, 149000, 149000⟩, ⟨4982, 5024, 4875584, 5040567, 149000, 149000⟩,
    ⟨5024, 5092, 4943513, 5096019, 149000, 149000⟩, ⟨5092, 5147, 4998964, 5138994, 149000, 149000⟩,
    ⟨5147, 5199, 5050257, 5198604, 149000, 149000⟩, ⟨5199, 5250, 5101550, 5241579, 149000, 149000⟩,
    ⟨5250, 5293, 5144525, 5276237, 149000, 149000⟩, ⟨5293, 5328, 5179183, 5310201, 149000, 149000⟩,
    ⟨5328, 5362, 5213147, 5340006, 149000, 149000⟩, ⟨5362, 5391, 5242952, 5357335, 149000, 149000⟩,
    ⟨5391, 5409, 5260281, 5382982, 149000, 149000⟩, ⟨5409, 5434, 5285927, 5417639, 149000, 149000⟩,
    ⟨5434, 5469, 5320585, 5452296, 149000, 149000⟩, ⟨5469, 5504, 5355242, 5503589, 149000, 149000⟩,
    ⟨5504, 5555, 5406535, 5546564, 149000, 149000⟩, ⟨5555, 5598, 5449510, 5598550, 149000, 149000⟩,
    ⟨5598, 5625, 5501496, 5607561, 149000, 149000⟩]

/-- The kernel-checked prefix bounds for 4889. -/
theorem theta4900_psi_4889_bounds :
    (4867279 : ℝ) / 1000 ≤ Chebyshev.psi 4889 ∧ Chebyshev.psi 4889 ≤ (4867973 : ℝ) / 1000 := by
  have hl : 2 ^ 7022 ≤ Nat.lcmUpto 4889 := by decide +kernel
  have hu : Nat.lcmUpto 4889 ≤ 2 ^ (7022 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 4913. -/
theorem theta4900_psi_4913_bounds :
    (4886687 : ℝ) / 1000 ≤ Chebyshev.psi 4913 ∧ Chebyshev.psi 4913 ≤ (4887381 : ℝ) / 1000 := by
  have hl : 2 ^ 7050 ≤ Nat.lcmUpto 4913 := by decide +kernel
  have hu : Nat.lcmUpto 4913 ≤ 2 ^ (7050 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 4919. -/
theorem theta4900_psi_4919_bounds :
    (4895698 : ℝ) / 1000 ≤ Chebyshev.psi 4919 ∧ Chebyshev.psi 4919 ≤ (4896392 : ℝ) / 1000 := by
  have hl : 2 ^ 7063 ≤ Nat.lcmUpto 4919 := by decide +kernel
  have hu : Nat.lcmUpto 4919 ≤ 2 ^ (7063 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 4943. -/
theorem theta4900_psi_4943_bounds :
    (4929662 : ℝ) / 1000 ≤ Chebyshev.psi 4943 ∧ Chebyshev.psi 4943 ≤ (4930356 : ℝ) / 1000 := by
  have hl : 2 ^ 7112 ≤ Nat.lcmUpto 4943 := by decide +kernel
  have hu : Nat.lcmUpto 4943 ≤ 2 ^ (7112 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 4973. -/
theorem theta4900_psi_4973_bounds :
    (4971944 : ℝ) / 1000 ≤ Chebyshev.psi 4973 ∧ Chebyshev.psi 4973 ≤ (4972638 : ℝ) / 1000 := by
  have hl : 2 ^ 7173 ≤ Nat.lcmUpto 4973 := by decide +kernel
  have hu : Nat.lcmUpto 4973 ≤ 2 ^ (7173 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 5023. -/
theorem theta4900_psi_5023_bounds :
    (5039873 : ℝ) / 1000 ≤ Chebyshev.psi 5023 ∧ Chebyshev.psi 5023 ≤ (5040567 : ℝ) / 1000 := by
  have hl : 2 ^ 7271 ≤ Nat.lcmUpto 5023 := by decide +kernel
  have hu : Nat.lcmUpto 5023 ≤ 2 ^ (7271 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 5087. -/
theorem theta4900_psi_5087_bounds :
    (5095324 : ℝ) / 1000 ≤ Chebyshev.psi 5087 ∧ Chebyshev.psi 5087 ≤ (5096019 : ℝ) / 1000 := by
  have hl : 2 ^ 7351 ≤ Nat.lcmUpto 5087 := by decide +kernel
  have hu : Nat.lcmUpto 5087 ≤ 2 ^ (7351 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 5119. -/
theorem theta4900_psi_5119_bounds :
    (5138300 : ℝ) / 1000 ≤ Chebyshev.psi 5119 ∧ Chebyshev.psi 5119 ≤ (5138994 : ℝ) / 1000 := by
  have hl : 2 ^ 7413 ≤ Nat.lcmUpto 5119 := by decide +kernel
  have hu : Nat.lcmUpto 5119 ≤ 2 ^ (7413 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 5147. -/
theorem theta4900_psi_5147_bounds :
    (5146617 : ℝ) / 1000 ≤ Chebyshev.psi 5147 ∧ Chebyshev.psi 5147 ≤ (5147311 : ℝ) / 1000 := by
  have hl : 2 ^ 7425 ≤ Nat.lcmUpto 5147 := by decide +kernel
  have hu : Nat.lcmUpto 5147 ≤ 2 ^ (7425 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 5197. -/
theorem theta4900_psi_5197_bounds :
    (5197910 : ℝ) / 1000 ≤ Chebyshev.psi 5197 ∧ Chebyshev.psi 5197 ≤ (5198604 : ℝ) / 1000 := by
  have hl : 2 ^ 7499 ≤ Nat.lcmUpto 5197 := by decide +kernel
  have hu : Nat.lcmUpto 5197 ≤ 2 ^ (7499 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 5237. -/
theorem theta4900_psi_5237_bounds :
    (5240885 : ℝ) / 1000 ≤ Chebyshev.psi 5237 ∧ Chebyshev.psi 5237 ≤ (5241579 : ℝ) / 1000 := by
  have hl : 2 ^ 7561 ≤ Nat.lcmUpto 5237 := by decide +kernel
  have hu : Nat.lcmUpto 5237 ≤ 2 ^ (7561 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 5281. -/
theorem theta4900_psi_5281_bounds :
    (5275543 : ℝ) / 1000 ≤ Chebyshev.psi 5281 ∧ Chebyshev.psi 5281 ≤ (5276237 : ℝ) / 1000 := by
  have hl : 2 ^ 7611 ≤ Nat.lcmUpto 5281 := by decide +kernel
  have hu : Nat.lcmUpto 5281 ≤ 2 ^ (7611 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 5323. -/
theorem theta4900_psi_5323_bounds :
    (5309507 : ℝ) / 1000 ≤ Chebyshev.psi 5323 ∧ Chebyshev.psi 5323 ≤ (5310201 : ℝ) / 1000 := by
  have hl : 2 ^ 7660 ≤ Nat.lcmUpto 5323 := by decide +kernel
  have hu : Nat.lcmUpto 5323 ≤ 2 ^ (7660 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 5351. -/
theorem theta4900_psi_5351_bounds :
    (5339312 : ℝ) / 1000 ≤ Chebyshev.psi 5351 ∧ Chebyshev.psi 5351 ≤ (5340006 : ℝ) / 1000 := by
  have hl : 2 ^ 7703 ≤ Nat.lcmUpto 5351 := by decide +kernel
  have hu : Nat.lcmUpto 5351 ≤ 2 ^ (7703 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 5387. -/
theorem theta4900_psi_5387_bounds :
    (5356641 : ℝ) / 1000 ≤ Chebyshev.psi 5387 ∧ Chebyshev.psi 5387 ≤ (5357335 : ℝ) / 1000 := by
  have hl : 2 ^ 7728 ≤ Nat.lcmUpto 5387 := by decide +kernel
  have hu : Nat.lcmUpto 5387 ≤ 2 ^ (7728 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 5407. -/
theorem theta4900_psi_5407_bounds :
    (5382287 : ℝ) / 1000 ≤ Chebyshev.psi 5407 ∧ Chebyshev.psi 5407 ≤ (5382982 : ℝ) / 1000 := by
  have hl : 2 ^ 7765 ≤ Nat.lcmUpto 5407 := by decide +kernel
  have hu : Nat.lcmUpto 5407 ≤ 2 ^ (7765 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 5431. -/
theorem theta4900_psi_5431_bounds :
    (5416945 : ℝ) / 1000 ≤ Chebyshev.psi 5431 ∧ Chebyshev.psi 5431 ≤ (5417639 : ℝ) / 1000 := by
  have hl : 2 ^ 7815 ≤ Nat.lcmUpto 5431 := by decide +kernel
  have hu : Nat.lcmUpto 5431 ≤ 2 ^ (7815 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 5449. -/
theorem theta4900_psi_5449_bounds :
    (5451602 : ℝ) / 1000 ≤ Chebyshev.psi 5449 ∧ Chebyshev.psi 5449 ≤ (5452296 : ℝ) / 1000 := by
  have hl : 2 ^ 7865 ≤ Nat.lcmUpto 5449 := by decide +kernel
  have hu : Nat.lcmUpto 5449 ≤ 2 ^ (7865 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 5503. -/
theorem theta4900_psi_5503_bounds :
    (5502895 : ℝ) / 1000 ≤ Chebyshev.psi 5503 ∧ Chebyshev.psi 5503 ≤ (5503589 : ℝ) / 1000 := by
  have hl : 2 ^ 7939 ≤ Nat.lcmUpto 5503 := by decide +kernel
  have hu : Nat.lcmUpto 5503 ≤ 2 ^ (7939 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 5531. -/
theorem theta4900_psi_5531_bounds :
    (5545870 : ℝ) / 1000 ≤ Chebyshev.psi 5531 ∧ Chebyshev.psi 5531 ≤ (5546564 : ℝ) / 1000 := by
  have hl : 2 ^ 8001 ≤ Nat.lcmUpto 5531 := by decide +kernel
  have hu : Nat.lcmUpto 5531 ≤ 2 ^ (8001 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 5591. -/
theorem theta4900_psi_5591_bounds :
    (5597856 : ℝ) / 1000 ≤ Chebyshev.psi 5591 ∧ Chebyshev.psi 5591 ≤ (5598550 : ℝ) / 1000 := by
  have hl : 2 ^ 8076 ≤ Nat.lcmUpto 5591 := by decide +kernel
  have hu : Nat.lcmUpto 5591 ≤ 2 ^ (8076 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 5623. -/
theorem theta4900_psi_5623_bounds :
    (5606867 : ℝ) / 1000 ≤ Chebyshev.psi 5623 ∧ Chebyshev.psi 5623 ≤ (5607561 : ℝ) / 1000 := by
  have hl : 2 ^ 8089 ≤ Nat.lcmUpto 5623 := by decide +kernel
  have hu : Nat.lcmUpto 5623 ≤ 2 ^ (8089 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- A rational certificate bounds the envelope from 4900 onward. -/
theorem theta4900_envelope {t : ℝ} (ht : 4900 ≤ t) :
    (149 : ℝ) ≤
      Real.sqrt t * (Real.log t * (Real.log t - Real.log (Real.log t)) / (8 * Real.pi)) := by
  have h :=
    lee_nosal_envelope_of_log_checks (N := 4900) (lo := 849 / 100) (hi := 850 / 100) (vlo :=
      214 / 100) (vhi := 215 / 100) (c := 149) (j := 13) (k := 4) (n := 32) (m := 32)
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by decide +kernel) (by decide +kernel) (by norm_num only)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact
    h.trans
      (lee_nosal_envelope_mono (x := 4900) (y := t)
        (Real.exp_one_lt_three.le.trans (by norm_num only)) ht)

/-- Every batch cell has a checked theta lower bound. -/
theorem theta4900_lower : ∀ r ∈ theta4900Cells, (r.lo : ℝ) / 1000 ≤ Chebyshev.theta r.a := by
  intro r hr
  simp only [theta4900Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  · change (4770919 : ℝ) / 1000 ≤ Chebyshev.theta (↑(4900 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_9636 (x := 4900) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 4889) (b := 4900) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta4900_psi_4889_bounds.1]
  · change (4799338 : ℝ) / 1000 ≤ Chebyshev.theta (↑(4919 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_9636 (x := 4919) (by norm_num only) (by norm_num only)
    linarith only [hd, theta4900_psi_4919_bounds.1]
  · change (4833302 : ℝ) / 1000 ≤ Chebyshev.theta (↑(4948 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_9636 (x := 4948) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 4943) (b := 4948) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta4900_psi_4943_bounds.1]
  · change (4875584 : ℝ) / 1000 ≤ Chebyshev.theta (↑(4982 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_9636 (x := 4982) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 4973) (b := 4982) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta4900_psi_4973_bounds.1]
  · change (4943513 : ℝ) / 1000 ≤ Chebyshev.theta (↑(5024 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_9636 (x := 5024) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 5023) (b := 5024) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta4900_psi_5023_bounds.1]
  · change (4998964 : ℝ) / 1000 ≤ Chebyshev.theta (↑(5092 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_9636 (x := 5092) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 5087) (b := 5092) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta4900_psi_5087_bounds.1]
  · change (5050257 : ℝ) / 1000 ≤ Chebyshev.theta (↑(5147 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_9636 (x := 5147) (by norm_num only) (by norm_num only)
    linarith only [hd, theta4900_psi_5147_bounds.1]
  · change (5101550 : ℝ) / 1000 ≤ Chebyshev.theta (↑(5199 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_9636 (x := 5199) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 5197) (b := 5199) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta4900_psi_5197_bounds.1]
  · change (5144525 : ℝ) / 1000 ≤ Chebyshev.theta (↑(5250 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_9636 (x := 5250) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 5237) (b := 5250) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta4900_psi_5237_bounds.1]
  · change (5179183 : ℝ) / 1000 ≤ Chebyshev.theta (↑(5293 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_9636 (x := 5293) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 5281) (b := 5293) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta4900_psi_5281_bounds.1]
  · change (5213147 : ℝ) / 1000 ≤ Chebyshev.theta (↑(5328 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_9636 (x := 5328) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 5323) (b := 5328) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta4900_psi_5323_bounds.1]
  · change (5242952 : ℝ) / 1000 ≤ Chebyshev.theta (↑(5362 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_9636 (x := 5362) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 5351) (b := 5362) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta4900_psi_5351_bounds.1]
  · change (5260281 : ℝ) / 1000 ≤ Chebyshev.theta (↑(5391 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_9636 (x := 5391) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 5387) (b := 5391) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta4900_psi_5387_bounds.1]
  · change (5285927 : ℝ) / 1000 ≤ Chebyshev.theta (↑(5409 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_9636 (x := 5409) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 5407) (b := 5409) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta4900_psi_5407_bounds.1]
  · change (5320585 : ℝ) / 1000 ≤ Chebyshev.theta (↑(5434 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_9636 (x := 5434) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 5431) (b := 5434) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta4900_psi_5431_bounds.1]
  · change (5355242 : ℝ) / 1000 ≤ Chebyshev.theta (↑(5469 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_9636 (x := 5469) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 5449) (b := 5469) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta4900_psi_5449_bounds.1]
  · change (5406535 : ℝ) / 1000 ≤ Chebyshev.theta (↑(5504 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_9636 (x := 5504) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 5503) (b := 5504) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta4900_psi_5503_bounds.1]
  · change (5449510 : ℝ) / 1000 ≤ Chebyshev.theta (↑(5555 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_9636 (x := 5555) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 5531) (b := 5555) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta4900_psi_5531_bounds.1]
  · change (5501496 : ℝ) / 1000 ≤ Chebyshev.theta (↑(5598 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_9636 (x := 5598) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 5591) (b := 5598) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta4900_psi_5591_bounds.1]

/-- Every batch cell has a checked theta upper bound. -/
theorem theta4900_upper :
    ∀ r ∈ theta4900Cells, Chebyshev.theta (r.b - 1 : ℕ) ≤ (r.hi : ℝ) / 1000 := by
  intro r hr
  simp only [theta4900Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  · change Chebyshev.theta (↑(4918 : ℕ) : ℝ) ≤ (4887381 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 4918
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 4913) (b := 4918) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta4900_psi_4913_bounds.2]
  · change Chebyshev.theta (↑(4947 : ℕ) : ℝ) ≤ (4930356 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 4947
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 4943) (b := 4947) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta4900_psi_4943_bounds.2]
  · change Chebyshev.theta (↑(4981 : ℕ) : ℝ) ≤ (4972638 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 4981
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 4973) (b := 4981) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta4900_psi_4973_bounds.2]
  · change Chebyshev.theta (↑(5023 : ℕ) : ℝ) ≤ (5040567 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 5023
    linarith only [hd, theta4900_psi_5023_bounds.2]
  · change Chebyshev.theta (↑(5091 : ℕ) : ℝ) ≤ (5096019 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 5091
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 5087) (b := 5091) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta4900_psi_5087_bounds.2]
  · change Chebyshev.theta (↑(5146 : ℕ) : ℝ) ≤ (5138994 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 5146
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 5119) (b := 5146) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta4900_psi_5119_bounds.2]
  · change Chebyshev.theta (↑(5198 : ℕ) : ℝ) ≤ (5198604 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 5198
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 5197) (b := 5198) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta4900_psi_5197_bounds.2]
  · change Chebyshev.theta (↑(5249 : ℕ) : ℝ) ≤ (5241579 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 5249
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 5237) (b := 5249) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta4900_psi_5237_bounds.2]
  · change Chebyshev.theta (↑(5292 : ℕ) : ℝ) ≤ (5276237 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 5292
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 5281) (b := 5292) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta4900_psi_5281_bounds.2]
  · change Chebyshev.theta (↑(5327 : ℕ) : ℝ) ≤ (5310201 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 5327
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 5323) (b := 5327) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta4900_psi_5323_bounds.2]
  · change Chebyshev.theta (↑(5361 : ℕ) : ℝ) ≤ (5340006 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 5361
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 5351) (b := 5361) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta4900_psi_5351_bounds.2]
  · change Chebyshev.theta (↑(5390 : ℕ) : ℝ) ≤ (5357335 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 5390
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 5387) (b := 5390) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta4900_psi_5387_bounds.2]
  · change Chebyshev.theta (↑(5408 : ℕ) : ℝ) ≤ (5382982 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 5408
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 5407) (b := 5408) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta4900_psi_5407_bounds.2]
  · change Chebyshev.theta (↑(5433 : ℕ) : ℝ) ≤ (5417639 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 5433
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 5431) (b := 5433) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta4900_psi_5431_bounds.2]
  · change Chebyshev.theta (↑(5468 : ℕ) : ℝ) ≤ (5452296 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 5468
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 5449) (b := 5468) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta4900_psi_5449_bounds.2]
  · change Chebyshev.theta (↑(5503 : ℕ) : ℝ) ≤ (5503589 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 5503
    linarith only [hd, theta4900_psi_5503_bounds.2]
  · change Chebyshev.theta (↑(5554 : ℕ) : ℝ) ≤ (5546564 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 5554
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 5531) (b := 5554) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta4900_psi_5531_bounds.2]
  · change Chebyshev.theta (↑(5597 : ℕ) : ℝ) ≤ (5598550 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 5597
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 5591) (b := 5597) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta4900_psi_5591_bounds.2]
  · change Chebyshev.theta (↑(5624 : ℕ) : ℝ) ≤ (5607561 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 5624
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 5623) (b := 5624) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta4900_psi_5623_bounds.2]

/-- The envelope bound applies at every cell a endpoint. -/
theorem theta4900_a :
    ∀ r ∈ theta4900Cells,
      (r.ca : ℝ) / 1000 ≤
        Real.sqrt r.a *
          (Real.log r.a * (Real.log r.a - Real.log (Real.log r.a)) / (8 * Real.pi)) := by
  intro r hr
  simp only [theta4900Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  · change
      (149000 : ℝ) / 1000 ≤
        Real.sqrt 4900 *
          (Real.log 4900 * (Real.log 4900 - Real.log (Real.log 4900)) / (8 * Real.pi))
    norm_num only
    exact theta4900_envelope (by norm_num only)
  · change
      (149000 : ℝ) / 1000 ≤
        Real.sqrt 4919 *
          (Real.log 4919 * (Real.log 4919 - Real.log (Real.log 4919)) / (8 * Real.pi))
    norm_num only
    exact theta4900_envelope (by norm_num only)
  · change
      (149000 : ℝ) / 1000 ≤
        Real.sqrt 4948 *
          (Real.log 4948 * (Real.log 4948 - Real.log (Real.log 4948)) / (8 * Real.pi))
    norm_num only
    exact theta4900_envelope (by norm_num only)
  · change
      (149000 : ℝ) / 1000 ≤
        Real.sqrt 4982 *
          (Real.log 4982 * (Real.log 4982 - Real.log (Real.log 4982)) / (8 * Real.pi))
    norm_num only
    exact theta4900_envelope (by norm_num only)
  · change
      (149000 : ℝ) / 1000 ≤
        Real.sqrt 5024 *
          (Real.log 5024 * (Real.log 5024 - Real.log (Real.log 5024)) / (8 * Real.pi))
    norm_num only
    exact theta4900_envelope (by norm_num only)
  · change
      (149000 : ℝ) / 1000 ≤
        Real.sqrt 5092 *
          (Real.log 5092 * (Real.log 5092 - Real.log (Real.log 5092)) / (8 * Real.pi))
    norm_num only
    exact theta4900_envelope (by norm_num only)
  · change
      (149000 : ℝ) / 1000 ≤
        Real.sqrt 5147 *
          (Real.log 5147 * (Real.log 5147 - Real.log (Real.log 5147)) / (8 * Real.pi))
    norm_num only
    exact theta4900_envelope (by norm_num only)
  · change
      (149000 : ℝ) / 1000 ≤
        Real.sqrt 5199 *
          (Real.log 5199 * (Real.log 5199 - Real.log (Real.log 5199)) / (8 * Real.pi))
    norm_num only
    exact theta4900_envelope (by norm_num only)
  · change
      (149000 : ℝ) / 1000 ≤
        Real.sqrt 5250 *
          (Real.log 5250 * (Real.log 5250 - Real.log (Real.log 5250)) / (8 * Real.pi))
    norm_num only
    exact theta4900_envelope (by norm_num only)
  · change
      (149000 : ℝ) / 1000 ≤
        Real.sqrt 5293 *
          (Real.log 5293 * (Real.log 5293 - Real.log (Real.log 5293)) / (8 * Real.pi))
    norm_num only
    exact theta4900_envelope (by norm_num only)
  · change
      (149000 : ℝ) / 1000 ≤
        Real.sqrt 5328 *
          (Real.log 5328 * (Real.log 5328 - Real.log (Real.log 5328)) / (8 * Real.pi))
    norm_num only
    exact theta4900_envelope (by norm_num only)
  · change
      (149000 : ℝ) / 1000 ≤
        Real.sqrt 5362 *
          (Real.log 5362 * (Real.log 5362 - Real.log (Real.log 5362)) / (8 * Real.pi))
    norm_num only
    exact theta4900_envelope (by norm_num only)
  · change
      (149000 : ℝ) / 1000 ≤
        Real.sqrt 5391 *
          (Real.log 5391 * (Real.log 5391 - Real.log (Real.log 5391)) / (8 * Real.pi))
    norm_num only
    exact theta4900_envelope (by norm_num only)
  · change
      (149000 : ℝ) / 1000 ≤
        Real.sqrt 5409 *
          (Real.log 5409 * (Real.log 5409 - Real.log (Real.log 5409)) / (8 * Real.pi))
    norm_num only
    exact theta4900_envelope (by norm_num only)
  · change
      (149000 : ℝ) / 1000 ≤
        Real.sqrt 5434 *
          (Real.log 5434 * (Real.log 5434 - Real.log (Real.log 5434)) / (8 * Real.pi))
    norm_num only
    exact theta4900_envelope (by norm_num only)
  · change
      (149000 : ℝ) / 1000 ≤
        Real.sqrt 5469 *
          (Real.log 5469 * (Real.log 5469 - Real.log (Real.log 5469)) / (8 * Real.pi))
    norm_num only
    exact theta4900_envelope (by norm_num only)
  · change
      (149000 : ℝ) / 1000 ≤
        Real.sqrt 5504 *
          (Real.log 5504 * (Real.log 5504 - Real.log (Real.log 5504)) / (8 * Real.pi))
    norm_num only
    exact theta4900_envelope (by norm_num only)
  · change
      (149000 : ℝ) / 1000 ≤
        Real.sqrt 5555 *
          (Real.log 5555 * (Real.log 5555 - Real.log (Real.log 5555)) / (8 * Real.pi))
    norm_num only
    exact theta4900_envelope (by norm_num only)
  · change
      (149000 : ℝ) / 1000 ≤
        Real.sqrt 5598 *
          (Real.log 5598 * (Real.log 5598 - Real.log (Real.log 5598)) / (8 * Real.pi))
    norm_num only
    exact theta4900_envelope (by norm_num only)

/-- The envelope bound applies at every cell b endpoint. -/
theorem theta4900_b :
    ∀ r ∈ theta4900Cells,
      (r.cb : ℝ) / 1000 ≤
        Real.sqrt r.b *
          (Real.log r.b * (Real.log r.b - Real.log (Real.log r.b)) / (8 * Real.pi)) := by
  intro r hr
  simp only [theta4900Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  · change
      (149000 : ℝ) / 1000 ≤
        Real.sqrt 4919 *
          (Real.log 4919 * (Real.log 4919 - Real.log (Real.log 4919)) / (8 * Real.pi))
    norm_num only
    exact theta4900_envelope (by norm_num only)
  · change
      (149000 : ℝ) / 1000 ≤
        Real.sqrt 4948 *
          (Real.log 4948 * (Real.log 4948 - Real.log (Real.log 4948)) / (8 * Real.pi))
    norm_num only
    exact theta4900_envelope (by norm_num only)
  · change
      (149000 : ℝ) / 1000 ≤
        Real.sqrt 4982 *
          (Real.log 4982 * (Real.log 4982 - Real.log (Real.log 4982)) / (8 * Real.pi))
    norm_num only
    exact theta4900_envelope (by norm_num only)
  · change
      (149000 : ℝ) / 1000 ≤
        Real.sqrt 5024 *
          (Real.log 5024 * (Real.log 5024 - Real.log (Real.log 5024)) / (8 * Real.pi))
    norm_num only
    exact theta4900_envelope (by norm_num only)
  · change
      (149000 : ℝ) / 1000 ≤
        Real.sqrt 5092 *
          (Real.log 5092 * (Real.log 5092 - Real.log (Real.log 5092)) / (8 * Real.pi))
    norm_num only
    exact theta4900_envelope (by norm_num only)
  · change
      (149000 : ℝ) / 1000 ≤
        Real.sqrt 5147 *
          (Real.log 5147 * (Real.log 5147 - Real.log (Real.log 5147)) / (8 * Real.pi))
    norm_num only
    exact theta4900_envelope (by norm_num only)
  · change
      (149000 : ℝ) / 1000 ≤
        Real.sqrt 5199 *
          (Real.log 5199 * (Real.log 5199 - Real.log (Real.log 5199)) / (8 * Real.pi))
    norm_num only
    exact theta4900_envelope (by norm_num only)
  · change
      (149000 : ℝ) / 1000 ≤
        Real.sqrt 5250 *
          (Real.log 5250 * (Real.log 5250 - Real.log (Real.log 5250)) / (8 * Real.pi))
    norm_num only
    exact theta4900_envelope (by norm_num only)
  · change
      (149000 : ℝ) / 1000 ≤
        Real.sqrt 5293 *
          (Real.log 5293 * (Real.log 5293 - Real.log (Real.log 5293)) / (8 * Real.pi))
    norm_num only
    exact theta4900_envelope (by norm_num only)
  · change
      (149000 : ℝ) / 1000 ≤
        Real.sqrt 5328 *
          (Real.log 5328 * (Real.log 5328 - Real.log (Real.log 5328)) / (8 * Real.pi))
    norm_num only
    exact theta4900_envelope (by norm_num only)
  · change
      (149000 : ℝ) / 1000 ≤
        Real.sqrt 5362 *
          (Real.log 5362 * (Real.log 5362 - Real.log (Real.log 5362)) / (8 * Real.pi))
    norm_num only
    exact theta4900_envelope (by norm_num only)
  · change
      (149000 : ℝ) / 1000 ≤
        Real.sqrt 5391 *
          (Real.log 5391 * (Real.log 5391 - Real.log (Real.log 5391)) / (8 * Real.pi))
    norm_num only
    exact theta4900_envelope (by norm_num only)
  · change
      (149000 : ℝ) / 1000 ≤
        Real.sqrt 5409 *
          (Real.log 5409 * (Real.log 5409 - Real.log (Real.log 5409)) / (8 * Real.pi))
    norm_num only
    exact theta4900_envelope (by norm_num only)
  · change
      (149000 : ℝ) / 1000 ≤
        Real.sqrt 5434 *
          (Real.log 5434 * (Real.log 5434 - Real.log (Real.log 5434)) / (8 * Real.pi))
    norm_num only
    exact theta4900_envelope (by norm_num only)
  · change
      (149000 : ℝ) / 1000 ≤
        Real.sqrt 5469 *
          (Real.log 5469 * (Real.log 5469 - Real.log (Real.log 5469)) / (8 * Real.pi))
    norm_num only
    exact theta4900_envelope (by norm_num only)
  · change
      (149000 : ℝ) / 1000 ≤
        Real.sqrt 5504 *
          (Real.log 5504 * (Real.log 5504 - Real.log (Real.log 5504)) / (8 * Real.pi))
    norm_num only
    exact theta4900_envelope (by norm_num only)
  · change
      (149000 : ℝ) / 1000 ≤
        Real.sqrt 5555 *
          (Real.log 5555 * (Real.log 5555 - Real.log (Real.log 5555)) / (8 * Real.pi))
    norm_num only
    exact theta4900_envelope (by norm_num only)
  · change
      (149000 : ℝ) / 1000 ≤
        Real.sqrt 5598 *
          (Real.log 5598 * (Real.log 5598 - Real.log (Real.log 5598)) / (8 * Real.pi))
    norm_num only
    exact theta4900_envelope (by norm_num only)
  · change
      (149000 : ℝ) / 1000 ≤
        Real.sqrt 5625 *
          (Real.log 5625 * (Real.log 5625 - Real.log (Real.log 5625)) / (8 * Real.pi))
    norm_num only
    exact theta4900_envelope (by norm_num only)

/-- The cells form a checked chain covering `[4900, 5625)`. -/
theorem theta4900_check : leeNosalChainCheck 4900 5625 theta4900Cells = true := by decide +kernel

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
