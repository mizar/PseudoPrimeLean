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
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSmallDefect4225
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalLogCheck
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalMonotone
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalChecker

/-! # Batch certificate for Lee–Nosal theta cells -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The local cells store endpoint bounds in thousandths. -/
private def batchCells : List LeeNosalCell :=
  [⟨3600, 3632, 3514937, 3639716, 118000, 118000⟩, ⟨3632, 3673, 3555832, 3672294, 118000, 118000⟩,
    ⟨3673, 3714, 3596728, 3721508, 118000, 118000⟩, ⟨3714, 3755, 3637624, 3758938, 118000, 118000⟩,
    ⟨3755, 3793, 3675054, 3791516, 118000, 118000⟩, ⟨3793, 3833, 3715949, 3833104, 118000, 118000⟩,
    ⟨3833, 3875, 3757538, 3874000, 118000, 118000⟩, ⟨3875, 3908, 3790116, 3907271, 118000, 118000⟩,
    ⟨3908, 3941, 3823387, 3957178, 118000, 118000⟩, ⟨3941, 3991, 3873294, 3989756, 118000, 118000⟩,
    ⟨3991, 4023, 3905872, 4039662, 118000, 118000⟩, ⟨4023, 4073, 3955778, 4072933, 118000, 118000⟩,
    ⟨4073, 4115, 3997367, 4123533, 118000, 118000⟩, ⟨4115, 4157, 4039649, 4165122, 118000, 118000⟩,
    ⟨4157, 4207, 4089556, 4198393, 118000, 118000⟩, ⟨4207, 4225, 4114509, 4223346, 118000, 118000⟩]

/-- The kernel-checked prefix bounds for 3593. -/
private theorem psi_3593_bounds :
    (3598127 : ℝ) / 1000 ≤ Chebyshev.psi 3593 ∧ Chebyshev.psi 3593 ≤ (3598821 : ℝ) / 1000 := by
  have hl : 2 ^ 5191 ≤ Nat.lcmUpto 3593 := by decide +kernel
  have hu : Nat.lcmUpto 3593 ≤ 2 ^ (5191 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 3631. -/
private theorem psi_3631_bounds :
    (3639022 : ℝ) / 1000 ≤ Chebyshev.psi 3631 ∧ Chebyshev.psi 3631 ≤ (3639716 : ℝ) / 1000 := by
  have hl : 2 ^ 5250 ≤ Nat.lcmUpto 3631 := by decide +kernel
  have hu : Nat.lcmUpto 3631 ≤ 2 ^ (5250 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 3671. -/
private theorem psi_3671_bounds :
    (3671600 : ℝ) / 1000 ≤ Chebyshev.psi 3671 ∧ Chebyshev.psi 3671 ≤ (3672294 : ℝ) / 1000 := by
  have hl : 2 ^ 5297 ≤ Nat.lcmUpto 3671 := by decide +kernel
  have hu : Nat.lcmUpto 3671 ≤ 2 ^ (5297 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 3673. -/
private theorem psi_3673_bounds :
    (3679918 : ℝ) / 1000 ≤ Chebyshev.psi 3673 ∧ Chebyshev.psi 3673 ≤ (3680612 : ℝ) / 1000 := by
  have hl : 2 ^ 5309 ≤ Nat.lcmUpto 3673 := by decide +kernel
  have hu : Nat.lcmUpto 3673 ≤ 2 ^ (5309 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 3709. -/
private theorem psi_3709_bounds :
    (3720814 : ℝ) / 1000 ≤ Chebyshev.psi 3709 ∧ Chebyshev.psi 3709 ≤ (3721508 : ℝ) / 1000 := by
  have hl : 2 ^ 5368 ≤ Nat.lcmUpto 3709 := by decide +kernel
  have hu : Nat.lcmUpto 3709 ≤ 2 ^ (5368 + 1) := by decide +kernel
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

/-- The kernel-checked prefix bounds for 3779. -/
private theorem psi_3779_bounds :
    (3790821 : ℝ) / 1000 ≤ Chebyshev.psi 3779 ∧ Chebyshev.psi 3779 ≤ (3791516 : ℝ) / 1000 := by
  have hl : 2 ^ 5469 ≤ Nat.lcmUpto 3779 := by decide +kernel
  have hu : Nat.lcmUpto 3779 ≤ 2 ^ (5469 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 3793. -/
private theorem psi_3793_bounds :
    (3799139 : ℝ) / 1000 ≤ Chebyshev.psi 3793 ∧ Chebyshev.psi 3793 ≤ (3799833 : ℝ) / 1000 := by
  have hl : 2 ^ 5481 ≤ Nat.lcmUpto 3793 := by decide +kernel
  have hu : Nat.lcmUpto 3793 ≤ 2 ^ (5481 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 3823. -/
private theorem psi_3823_bounds :
    (3832410 : ℝ) / 1000 ≤ Chebyshev.psi 3823 ∧ Chebyshev.psi 3823 ≤ (3833104 : ℝ) / 1000 := by
  have hl : 2 ^ 5529 ≤ Nat.lcmUpto 3823 := by decide +kernel
  have hu : Nat.lcmUpto 3823 ≤ 2 ^ (5529 + 1) := by decide +kernel
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

/-- The kernel-checked prefix bounds for 3863. -/
private theorem psi_3863_bounds :
    (3873306 : ℝ) / 1000 ≤ Chebyshev.psi 3863 ∧ Chebyshev.psi 3863 ≤ (3874000 : ℝ) / 1000 := by
  have hl : 2 ^ 5588 ≤ Nat.lcmUpto 3863 := by decide +kernel
  have hu : Nat.lcmUpto 3863 ≤ 2 ^ (5588 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 3907. -/
private theorem psi_3907_bounds :
    (3906577 : ℝ) / 1000 ≤ Chebyshev.psi 3907 ∧ Chebyshev.psi 3907 ≤ (3907271 : ℝ) / 1000 := by
  have hl : 2 ^ 5636 ≤ Nat.lcmUpto 3907 := by decide +kernel
  have hu : Nat.lcmUpto 3907 ≤ 2 ^ (5636 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 3931. -/
private theorem psi_3931_bounds :
    (3956484 : ℝ) / 1000 ≤ Chebyshev.psi 3931 ∧ Chebyshev.psi 3931 ≤ (3957178 : ℝ) / 1000 := by
  have hl : 2 ^ 5708 ≤ Nat.lcmUpto 3931 := by decide +kernel
  have hu : Nat.lcmUpto 3931 ≤ 2 ^ (5708 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 3989. -/
private theorem psi_3989_bounds :
    (3989062 : ℝ) / 1000 ≤ Chebyshev.psi 3989 ∧ Chebyshev.psi 3989 ≤ (3989756 : ℝ) / 1000 := by
  have hl : 2 ^ 5755 ≤ Nat.lcmUpto 3989 := by decide +kernel
  have hu : Nat.lcmUpto 3989 ≤ 2 ^ (5755 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 4021. -/
private theorem psi_4021_bounds :
    (4038968 : ℝ) / 1000 ≤ Chebyshev.psi 4021 ∧ Chebyshev.psi 4021 ≤ (4039662 : ℝ) / 1000 := by
  have hl : 2 ^ 5827 ≤ Nat.lcmUpto 4021 := by decide +kernel
  have hu : Nat.lcmUpto 4021 ≤ 2 ^ (5827 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 4057. -/
private theorem psi_4057_bounds :
    (4072239 : ℝ) / 1000 ≤ Chebyshev.psi 4057 ∧ Chebyshev.psi 4057 ≤ (4072933 : ℝ) / 1000 := by
  have hl : 2 ^ 5875 ≤ Nat.lcmUpto 4057 := by decide +kernel
  have hu : Nat.lcmUpto 4057 ≤ 2 ^ (5875 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 4073. -/
private theorem psi_4073_bounds :
    (4080557 : ℝ) / 1000 ≤ Chebyshev.psi 4073 ∧ Chebyshev.psi 4073 ≤ (4081251 : ℝ) / 1000 := by
  have hl : 2 ^ 5887 ≤ Nat.lcmUpto 4073 := by decide +kernel
  have hu : Nat.lcmUpto 4073 ≤ 2 ^ (5887 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 4111. -/
private theorem psi_4111_bounds :
    (4122839 : ℝ) / 1000 ≤ Chebyshev.psi 4111 ∧ Chebyshev.psi 4111 ≤ (4123533 : ℝ) / 1000 := by
  have hl : 2 ^ 5948 ≤ Nat.lcmUpto 4111 := by decide +kernel
  have hu : Nat.lcmUpto 4111 ≤ 2 ^ (5948 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 4153. -/
private theorem psi_4153_bounds :
    (4164428 : ℝ) / 1000 ≤ Chebyshev.psi 4153 ∧ Chebyshev.psi 4153 ≤ (4165122 : ℝ) / 1000 := by
  have hl : 2 ^ 6008 ≤ Nat.lcmUpto 4153 := by decide +kernel
  have hu : Nat.lcmUpto 4153 ≤ 2 ^ (6008 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 4157. -/
private theorem psi_4157_bounds :
    (4172746 : ℝ) / 1000 ≤ Chebyshev.psi 4157 ∧ Chebyshev.psi 4157 ≤ (4173440 : ℝ) / 1000 := by
  have hl : 2 ^ 6020 ≤ Nat.lcmUpto 4157 := by decide +kernel
  have hu : Nat.lcmUpto 4157 ≤ 2 ^ (6020 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 4201. -/
private theorem psi_4201_bounds :
    (4197699 : ℝ) / 1000 ≤ Chebyshev.psi 4201 ∧ Chebyshev.psi 4201 ≤ (4198393 : ℝ) / 1000 := by
  have hl : 2 ^ 6056 ≤ Nat.lcmUpto 4201 := by decide +kernel
  have hu : Nat.lcmUpto 4201 ≤ 2 ^ (6056 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 4219. -/
private theorem psi_4219_bounds :
    (4222652 : ℝ) / 1000 ≤ Chebyshev.psi 4219 ∧ Chebyshev.psi 4219 ≤ (4223346 : ℝ) / 1000 := by
  have hl : 2 ^ 6092 ≤ Nat.lcmUpto 4219 := by decide +kernel
  have hu : Nat.lcmUpto 4219 ≤ 2 ^ (6092 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- A rational certificate bounds the envelope from 3600 onward. -/
private theorem batch_envelope {t : ℝ} (ht : 3600 ≤ t) :
    (118 : ℝ) ≤
      Real.sqrt t * (Real.log t * (Real.log t - Real.log (Real.log t)) / (8 * Real.pi)) := by
  have h :=
    lee_nosal_envelope_of_log_checks (N := 3600) (lo := 818 / 100) (hi := 819 / 100) (vlo :=
      210 / 100) (vhi := 211 / 100) (c := 118) (j := 12) (k := 4) (n := 32) (m := 32)
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by decide +kernel) (by decide +kernel) (by norm_num only)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact
    h.trans
      (lee_nosal_envelope_mono (x := 3600) (y := t)
        (Real.exp_one_lt_three.le.trans (by norm_num only)) ht)

/-- Every batch cell has a checked theta lower bound. -/
private theorem batch_lower : ∀ r ∈ batchCells, (r.lo : ℝ) / 1000 ≤ Chebyshev.theta r.a := by
  intro r hr
  simp only [batchCells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · change (3514937 : ℝ) / 1000 ≤ Chebyshev.theta (↑(3600 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_8319 (x := 3600) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3593) (b := 3600) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3593_bounds.1]
  · change (3555832 : ℝ) / 1000 ≤ Chebyshev.theta (↑(3632 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_8319 (x := 3632) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3631) (b := 3632) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3631_bounds.1]
  · change (3596728 : ℝ) / 1000 ≤ Chebyshev.theta (↑(3673 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_8319 (x := 3673) (by norm_num only) (by norm_num only)
    linarith only [hd, psi_3673_bounds.1]
  · change (3637624 : ℝ) / 1000 ≤ Chebyshev.theta (↑(3714 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_8319 (x := 3714) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3709) (b := 3714) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3709_bounds.1]
  · change (3675054 : ℝ) / 1000 ≤ Chebyshev.theta (↑(3755 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_8319 (x := 3755) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3739) (b := 3755) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3739_bounds.1]
  · change (3715949 : ℝ) / 1000 ≤ Chebyshev.theta (↑(3793 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_8319 (x := 3793) (by norm_num only) (by norm_num only)
    linarith only [hd, psi_3793_bounds.1]
  · change (3757538 : ℝ) / 1000 ≤ Chebyshev.theta (↑(3833 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_8319 (x := 3833) (by norm_num only) (by norm_num only)
    linarith only [hd, psi_3833_bounds.1]
  · change (3790116 : ℝ) / 1000 ≤ Chebyshev.theta (↑(3875 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_8319 (x := 3875) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3863) (b := 3875) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3863_bounds.1]
  · change (3823387 : ℝ) / 1000 ≤ Chebyshev.theta (↑(3908 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_8319 (x := 3908) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3907) (b := 3908) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3907_bounds.1]
  · change (3873294 : ℝ) / 1000 ≤ Chebyshev.theta (↑(3941 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_8319 (x := 3941) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3931) (b := 3941) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3931_bounds.1]
  · change (3905872 : ℝ) / 1000 ≤ Chebyshev.theta (↑(3991 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_8319 (x := 3991) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3989) (b := 3991) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3989_bounds.1]
  · change (3955778 : ℝ) / 1000 ≤ Chebyshev.theta (↑(4023 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_8319 (x := 4023) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 4021) (b := 4023) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_4021_bounds.1]
  · change (3997367 : ℝ) / 1000 ≤ Chebyshev.theta (↑(4073 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_8319 (x := 4073) (by norm_num only) (by norm_num only)
    linarith only [hd, psi_4073_bounds.1]
  · change (4039649 : ℝ) / 1000 ≤ Chebyshev.theta (↑(4115 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_8319 (x := 4115) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 4111) (b := 4115) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_4111_bounds.1]
  · change (4089556 : ℝ) / 1000 ≤ Chebyshev.theta (↑(4157 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_8319 (x := 4157) (by norm_num only) (by norm_num only)
    linarith only [hd, psi_4157_bounds.1]
  · change (4114509 : ℝ) / 1000 ≤ Chebyshev.theta (↑(4207 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_8319 (x := 4207) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 4201) (b := 4207) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_4201_bounds.1]

/-- Every batch cell has a checked theta upper bound. -/
private theorem batch_upper :
    ∀ r ∈ batchCells, Chebyshev.theta (r.b - 1 : ℕ) ≤ (r.hi : ℝ) / 1000 := by
  intro r hr
  simp only [batchCells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · change Chebyshev.theta (↑(3631 : ℕ) : ℝ) ≤ (3639716 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 3631
    linarith only [hd, psi_3631_bounds.2]
  · change Chebyshev.theta (↑(3672 : ℕ) : ℝ) ≤ (3672294 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 3672
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3671) (b := 3672) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3671_bounds.2]
  · change Chebyshev.theta (↑(3713 : ℕ) : ℝ) ≤ (3721508 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 3713
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3709) (b := 3713) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3709_bounds.2]
  · change Chebyshev.theta (↑(3754 : ℕ) : ℝ) ≤ (3758938 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 3754
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3739) (b := 3754) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3739_bounds.2]
  · change Chebyshev.theta (↑(3792 : ℕ) : ℝ) ≤ (3791516 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 3792
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3779) (b := 3792) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3779_bounds.2]
  · change Chebyshev.theta (↑(3832 : ℕ) : ℝ) ≤ (3833104 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 3832
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3823) (b := 3832) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3823_bounds.2]
  · change Chebyshev.theta (↑(3874 : ℕ) : ℝ) ≤ (3874000 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 3874
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3863) (b := 3874) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3863_bounds.2]
  · change Chebyshev.theta (↑(3907 : ℕ) : ℝ) ≤ (3907271 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 3907
    linarith only [hd, psi_3907_bounds.2]
  · change Chebyshev.theta (↑(3940 : ℕ) : ℝ) ≤ (3957178 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 3940
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3931) (b := 3940) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3931_bounds.2]
  · change Chebyshev.theta (↑(3990 : ℕ) : ℝ) ≤ (3989756 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 3990
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3989) (b := 3990) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3989_bounds.2]
  · change Chebyshev.theta (↑(4022 : ℕ) : ℝ) ≤ (4039662 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 4022
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 4021) (b := 4022) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_4021_bounds.2]
  · change Chebyshev.theta (↑(4072 : ℕ) : ℝ) ≤ (4072933 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 4072
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 4057) (b := 4072) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_4057_bounds.2]
  · change Chebyshev.theta (↑(4114 : ℕ) : ℝ) ≤ (4123533 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 4114
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 4111) (b := 4114) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_4111_bounds.2]
  · change Chebyshev.theta (↑(4156 : ℕ) : ℝ) ≤ (4165122 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 4156
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 4153) (b := 4156) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_4153_bounds.2]
  · change Chebyshev.theta (↑(4206 : ℕ) : ℝ) ≤ (4198393 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 4206
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 4201) (b := 4206) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_4201_bounds.2]
  · change Chebyshev.theta (↑(4224 : ℕ) : ℝ) ≤ (4223346 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 4224
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 4219) (b := 4224) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_4219_bounds.2]

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
      (118000 : ℝ) / 1000 ≤
        Real.sqrt 3600 *
          (Real.log 3600 * (Real.log 3600 - Real.log (Real.log 3600)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (118000 : ℝ) / 1000 ≤
        Real.sqrt 3632 *
          (Real.log 3632 * (Real.log 3632 - Real.log (Real.log 3632)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (118000 : ℝ) / 1000 ≤
        Real.sqrt 3673 *
          (Real.log 3673 * (Real.log 3673 - Real.log (Real.log 3673)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (118000 : ℝ) / 1000 ≤
        Real.sqrt 3714 *
          (Real.log 3714 * (Real.log 3714 - Real.log (Real.log 3714)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (118000 : ℝ) / 1000 ≤
        Real.sqrt 3755 *
          (Real.log 3755 * (Real.log 3755 - Real.log (Real.log 3755)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (118000 : ℝ) / 1000 ≤
        Real.sqrt 3793 *
          (Real.log 3793 * (Real.log 3793 - Real.log (Real.log 3793)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (118000 : ℝ) / 1000 ≤
        Real.sqrt 3833 *
          (Real.log 3833 * (Real.log 3833 - Real.log (Real.log 3833)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (118000 : ℝ) / 1000 ≤
        Real.sqrt 3875 *
          (Real.log 3875 * (Real.log 3875 - Real.log (Real.log 3875)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (118000 : ℝ) / 1000 ≤
        Real.sqrt 3908 *
          (Real.log 3908 * (Real.log 3908 - Real.log (Real.log 3908)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (118000 : ℝ) / 1000 ≤
        Real.sqrt 3941 *
          (Real.log 3941 * (Real.log 3941 - Real.log (Real.log 3941)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (118000 : ℝ) / 1000 ≤
        Real.sqrt 3991 *
          (Real.log 3991 * (Real.log 3991 - Real.log (Real.log 3991)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (118000 : ℝ) / 1000 ≤
        Real.sqrt 4023 *
          (Real.log 4023 * (Real.log 4023 - Real.log (Real.log 4023)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (118000 : ℝ) / 1000 ≤
        Real.sqrt 4073 *
          (Real.log 4073 * (Real.log 4073 - Real.log (Real.log 4073)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (118000 : ℝ) / 1000 ≤
        Real.sqrt 4115 *
          (Real.log 4115 * (Real.log 4115 - Real.log (Real.log 4115)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (118000 : ℝ) / 1000 ≤
        Real.sqrt 4157 *
          (Real.log 4157 * (Real.log 4157 - Real.log (Real.log 4157)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (118000 : ℝ) / 1000 ≤
        Real.sqrt 4207 *
          (Real.log 4207 * (Real.log 4207 - Real.log (Real.log 4207)) / (8 * Real.pi))
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
      (118000 : ℝ) / 1000 ≤
        Real.sqrt 3632 *
          (Real.log 3632 * (Real.log 3632 - Real.log (Real.log 3632)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (118000 : ℝ) / 1000 ≤
        Real.sqrt 3673 *
          (Real.log 3673 * (Real.log 3673 - Real.log (Real.log 3673)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (118000 : ℝ) / 1000 ≤
        Real.sqrt 3714 *
          (Real.log 3714 * (Real.log 3714 - Real.log (Real.log 3714)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (118000 : ℝ) / 1000 ≤
        Real.sqrt 3755 *
          (Real.log 3755 * (Real.log 3755 - Real.log (Real.log 3755)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (118000 : ℝ) / 1000 ≤
        Real.sqrt 3793 *
          (Real.log 3793 * (Real.log 3793 - Real.log (Real.log 3793)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (118000 : ℝ) / 1000 ≤
        Real.sqrt 3833 *
          (Real.log 3833 * (Real.log 3833 - Real.log (Real.log 3833)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (118000 : ℝ) / 1000 ≤
        Real.sqrt 3875 *
          (Real.log 3875 * (Real.log 3875 - Real.log (Real.log 3875)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (118000 : ℝ) / 1000 ≤
        Real.sqrt 3908 *
          (Real.log 3908 * (Real.log 3908 - Real.log (Real.log 3908)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (118000 : ℝ) / 1000 ≤
        Real.sqrt 3941 *
          (Real.log 3941 * (Real.log 3941 - Real.log (Real.log 3941)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (118000 : ℝ) / 1000 ≤
        Real.sqrt 3991 *
          (Real.log 3991 * (Real.log 3991 - Real.log (Real.log 3991)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (118000 : ℝ) / 1000 ≤
        Real.sqrt 4023 *
          (Real.log 4023 * (Real.log 4023 - Real.log (Real.log 4023)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (118000 : ℝ) / 1000 ≤
        Real.sqrt 4073 *
          (Real.log 4073 * (Real.log 4073 - Real.log (Real.log 4073)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (118000 : ℝ) / 1000 ≤
        Real.sqrt 4115 *
          (Real.log 4115 * (Real.log 4115 - Real.log (Real.log 4115)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (118000 : ℝ) / 1000 ≤
        Real.sqrt 4157 *
          (Real.log 4157 * (Real.log 4157 - Real.log (Real.log 4157)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (118000 : ℝ) / 1000 ≤
        Real.sqrt 4207 *
          (Real.log 4207 * (Real.log 4207 - Real.log (Real.log 4207)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (118000 : ℝ) / 1000 ≤
        Real.sqrt 4225 *
          (Real.log 4225 * (Real.log 4225 - Real.log (Real.log 4225)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)

/-- The checked batch proves the Lee–Nosal theta estimate on `[3600, 4225)`. -/
theorem theta_lee_nosal_3600_4225 {x : ℝ} (ha : 3600 ≤ x) (hb : x < 4225) :
    |Chebyshev.theta x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  exact
    lee_nosal_chain_sound Chebyshev.theta_mono Chebyshev.theta_eq_theta_coe_floor
      (by decide +kernel) batch_lower batch_upper batch_a batch_b ha hb

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
