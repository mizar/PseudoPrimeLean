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
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevDefect2900
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalLogCheck
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalMonotone
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalChecker

/-! # Batch certificate for Lee–Nosal theta cells -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The local cells store endpoint bounds in thousandths. -/
private def batchCells : List LeeNosalCell :=
  [⟨2704, 2714, 2620440, 2726842, 94000, 94000⟩, ⟨2714, 2738, 2644007, 2750409, 94000, 94000⟩,
    ⟨2738, 2761, 2667574, 2774669, 94000, 94000⟩, ⟨2761, 2785, 2691835, 2790611, 94000, 94000⟩,
    ⟨2785, 2801, 2707777, 2814178, 94000, 94000⟩, ⟨2801, 2832, 2738969, 2841904, 94000, 94000⟩,
    ⟨2832, 2853, 2759070, 2873789, 94000, 94000⟩, ⟨2853, 2884, 2790955, 2897356, 94000, 94000⟩,
    ⟨2884, 2900, 2814522, 2913298, 94000, 94000⟩]

/-- The kernel-checked prefix bounds for 2699. -/
private theorem psi_2699_bounds :
    (2702580 : ℝ) / 1000 ≤ Chebyshev.psi 2699 ∧ Chebyshev.psi 2699 ≤ (2703275 : ℝ) / 1000 := by
  have hl : 2 ^ 3899 ≤ Nat.lcmUpto 2699 := by decide +kernel
  have hu : Nat.lcmUpto 2699 ≤ 2 ^ (3899 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 2713. -/
private theorem psi_2713_bounds :
    (2726147 : ℝ) / 1000 ≤ Chebyshev.psi 2713 ∧ Chebyshev.psi 2713 ≤ (2726842 : ℝ) / 1000 := by
  have hl : 2 ^ 3933 ≤ Nat.lcmUpto 2713 := by decide +kernel
  have hu : Nat.lcmUpto 2713 ≤ 2 ^ (3933 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 2731. -/
private theorem psi_2731_bounds :
    (2749714 : ℝ) / 1000 ≤ Chebyshev.psi 2731 ∧ Chebyshev.psi 2731 ≤ (2750409 : ℝ) / 1000 := by
  have hl : 2 ^ 3967 ≤ Nat.lcmUpto 2731 := by decide +kernel
  have hu : Nat.lcmUpto 2731 ≤ 2 ^ (3967 + 1) := by decide +kernel
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

/-- The kernel-checked prefix bounds for 2777. -/
private theorem psi_2777_bounds :
    (2789917 : ℝ) / 1000 ≤ Chebyshev.psi 2777 ∧ Chebyshev.psi 2777 ≤ (2790611 : ℝ) / 1000 := by
  have hl : 2 ^ 4025 ≤ Nat.lcmUpto 2777 := by decide +kernel
  have hu : Nat.lcmUpto 2777 ≤ 2 ^ (4025 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 2797. -/
private theorem psi_2797_bounds :
    (2813484 : ℝ) / 1000 ≤ Chebyshev.psi 2797 ∧ Chebyshev.psi 2797 ≤ (2814178 : ℝ) / 1000 := by
  have hl : 2 ^ 4059 ≤ Nat.lcmUpto 2797 := by decide +kernel
  have hu : Nat.lcmUpto 2797 ≤ 2 ^ (4059 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 2801. -/
private theorem psi_2801_bounds :
    (2821109 : ℝ) / 1000 ≤ Chebyshev.psi 2801 ∧ Chebyshev.psi 2801 ≤ (2821803 : ℝ) / 1000 := by
  have hl : 2 ^ 4070 ≤ Nat.lcmUpto 2801 := by decide +kernel
  have hu : Nat.lcmUpto 2801 ≤ 2 ^ (4070 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 2819. -/
private theorem psi_2819_bounds :
    (2841210 : ℝ) / 1000 ≤ Chebyshev.psi 2819 ∧ Chebyshev.psi 2819 ≤ (2841904 : ℝ) / 1000 := by
  have hl : 2 ^ 4099 ≤ Nat.lcmUpto 2819 := by decide +kernel
  have hu : Nat.lcmUpto 2819 ≤ 2 ^ (4099 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 2851. -/
private theorem psi_2851_bounds :
    (2873095 : ℝ) / 1000 ≤ Chebyshev.psi 2851 ∧ Chebyshev.psi 2851 ≤ (2873789 : ℝ) / 1000 := by
  have hl : 2 ^ 4145 ≤ Nat.lcmUpto 2851 := by decide +kernel
  have hu : Nat.lcmUpto 2851 ≤ 2 ^ (4145 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 2879. -/
private theorem psi_2879_bounds :
    (2896662 : ℝ) / 1000 ≤ Chebyshev.psi 2879 ∧ Chebyshev.psi 2879 ≤ (2897356 : ℝ) / 1000 := by
  have hl : 2 ^ 4179 ≤ Nat.lcmUpto 2879 := by decide +kernel
  have hu : Nat.lcmUpto 2879 ≤ 2 ^ (4179 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 2897. -/
private theorem psi_2897_bounds :
    (2912604 : ℝ) / 1000 ≤ Chebyshev.psi 2897 ∧ Chebyshev.psi 2897 ≤ (2913298 : ℝ) / 1000 := by
  have hl : 2 ^ 4202 ≤ Nat.lcmUpto 2897 := by decide +kernel
  have hu : Nat.lcmUpto 2897 ≤ 2 ^ (4202 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- A rational certificate bounds the envelope from 2657 onward. -/
private theorem batch_envelope {t : ℝ} (ht : 2657 ≤ t) :
    (94 : ℝ) ≤
      Real.sqrt t * (Real.log t * (Real.log t - Real.log (Real.log t)) / (8 * Real.pi)) := by
  have h :=
    lee_nosal_envelope_of_log_checks (N := 2657) (lo := 7884 / 1000) (hi := 7885 / 1000) (vlo :=
      2064 / 1000) (vhi := 2066 / 1000) (c := 94) (j := 12) (k := 4) (n := 32) (m := 32)
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by decide +kernel) (by decide +kernel) (by norm_num only)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact
    h.trans
      (lee_nosal_envelope_mono (x := 2657) (y := t)
        (Real.exp_one_lt_three.le.trans (by norm_num only)) ht)

/-- Every batch cell has a checked theta lower bound. -/
private theorem batch_lower : ∀ r ∈ batchCells, (r.lo : ℝ) / 1000 ≤ Chebyshev.theta r.a := by
  intro r hr
  simp only [batchCells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change (2620440 : ℝ) / 1000 ≤ Chebyshev.theta (↑(2704 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_8214 (x := 2704) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 2699) (b := 2704) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_2699_bounds.1]
  · change (2644007 : ℝ) / 1000 ≤ Chebyshev.theta (↑(2714 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_8214 (x := 2714) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 2713) (b := 2714) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_2713_bounds.1]
  · change (2667574 : ℝ) / 1000 ≤ Chebyshev.theta (↑(2738 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_8214 (x := 2738) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 2731) (b := 2738) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_2731_bounds.1]
  · change (2691835 : ℝ) / 1000 ≤ Chebyshev.theta (↑(2761 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_8214 (x := 2761) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 2753) (b := 2761) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_2753_bounds.1]
  · change (2707777 : ℝ) / 1000 ≤ Chebyshev.theta (↑(2785 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_8214 (x := 2785) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 2777) (b := 2785) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_2777_bounds.1]
  · change (2738969 : ℝ) / 1000 ≤ Chebyshev.theta (↑(2801 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_8214 (x := 2801) (by norm_num only) (by norm_num only)
    linarith only [hd, psi_2801_bounds.1]
  · change (2759070 : ℝ) / 1000 ≤ Chebyshev.theta (↑(2832 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_8214 (x := 2832) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 2819) (b := 2832) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_2819_bounds.1]
  · change (2790955 : ℝ) / 1000 ≤ Chebyshev.theta (↑(2853 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_8214 (x := 2853) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 2851) (b := 2853) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_2851_bounds.1]
  · change (2814522 : ℝ) / 1000 ≤ Chebyshev.theta (↑(2884 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_8214 (x := 2884) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 2879) (b := 2884) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_2879_bounds.1]

/-- Every batch cell has a checked theta upper bound. -/
private theorem batch_upper :
    ∀ r ∈ batchCells, Chebyshev.theta (r.b - 1 : ℕ) ≤ (r.hi : ℝ) / 1000 := by
  intro r hr
  simp only [batchCells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change Chebyshev.theta (↑(2713 : ℕ) : ℝ) ≤ (2726842 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 2713
    linarith only [hd, psi_2713_bounds.2]
  · change Chebyshev.theta (↑(2737 : ℕ) : ℝ) ≤ (2750409 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 2737
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 2731) (b := 2737) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_2731_bounds.2]
  · change Chebyshev.theta (↑(2760 : ℕ) : ℝ) ≤ (2774669 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 2760
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 2753) (b := 2760) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_2753_bounds.2]
  · change Chebyshev.theta (↑(2784 : ℕ) : ℝ) ≤ (2790611 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 2784
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 2777) (b := 2784) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_2777_bounds.2]
  · change Chebyshev.theta (↑(2800 : ℕ) : ℝ) ≤ (2814178 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 2800
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 2797) (b := 2800) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_2797_bounds.2]
  · change Chebyshev.theta (↑(2831 : ℕ) : ℝ) ≤ (2841904 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 2831
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 2819) (b := 2831) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_2819_bounds.2]
  · change Chebyshev.theta (↑(2852 : ℕ) : ℝ) ≤ (2873789 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 2852
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 2851) (b := 2852) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_2851_bounds.2]
  · change Chebyshev.theta (↑(2883 : ℕ) : ℝ) ≤ (2897356 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 2883
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 2879) (b := 2883) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_2879_bounds.2]
  · change Chebyshev.theta (↑(2899 : ℕ) : ℝ) ≤ (2913298 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 2899
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 2897) (b := 2899) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_2897_bounds.2]

/-- The envelope bound applies at every cell a endpoint. -/
private theorem batch_a :
    ∀ r ∈ batchCells,
      (r.ca : ℝ) / 1000 ≤
        Real.sqrt r.a *
          (Real.log r.a * (Real.log r.a - Real.log (Real.log r.a)) / (8 * Real.pi)) := by
  intro r hr
  simp only [batchCells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change
      (94000 : ℝ) / 1000 ≤
        Real.sqrt 2704 *
          (Real.log 2704 * (Real.log 2704 - Real.log (Real.log 2704)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (94000 : ℝ) / 1000 ≤
        Real.sqrt 2714 *
          (Real.log 2714 * (Real.log 2714 - Real.log (Real.log 2714)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (94000 : ℝ) / 1000 ≤
        Real.sqrt 2738 *
          (Real.log 2738 * (Real.log 2738 - Real.log (Real.log 2738)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (94000 : ℝ) / 1000 ≤
        Real.sqrt 2761 *
          (Real.log 2761 * (Real.log 2761 - Real.log (Real.log 2761)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (94000 : ℝ) / 1000 ≤
        Real.sqrt 2785 *
          (Real.log 2785 * (Real.log 2785 - Real.log (Real.log 2785)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (94000 : ℝ) / 1000 ≤
        Real.sqrt 2801 *
          (Real.log 2801 * (Real.log 2801 - Real.log (Real.log 2801)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (94000 : ℝ) / 1000 ≤
        Real.sqrt 2832 *
          (Real.log 2832 * (Real.log 2832 - Real.log (Real.log 2832)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (94000 : ℝ) / 1000 ≤
        Real.sqrt 2853 *
          (Real.log 2853 * (Real.log 2853 - Real.log (Real.log 2853)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (94000 : ℝ) / 1000 ≤
        Real.sqrt 2884 *
          (Real.log 2884 * (Real.log 2884 - Real.log (Real.log 2884)) / (8 * Real.pi))
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
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change
      (94000 : ℝ) / 1000 ≤
        Real.sqrt 2714 *
          (Real.log 2714 * (Real.log 2714 - Real.log (Real.log 2714)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (94000 : ℝ) / 1000 ≤
        Real.sqrt 2738 *
          (Real.log 2738 * (Real.log 2738 - Real.log (Real.log 2738)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (94000 : ℝ) / 1000 ≤
        Real.sqrt 2761 *
          (Real.log 2761 * (Real.log 2761 - Real.log (Real.log 2761)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (94000 : ℝ) / 1000 ≤
        Real.sqrt 2785 *
          (Real.log 2785 * (Real.log 2785 - Real.log (Real.log 2785)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (94000 : ℝ) / 1000 ≤
        Real.sqrt 2801 *
          (Real.log 2801 * (Real.log 2801 - Real.log (Real.log 2801)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (94000 : ℝ) / 1000 ≤
        Real.sqrt 2832 *
          (Real.log 2832 * (Real.log 2832 - Real.log (Real.log 2832)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (94000 : ℝ) / 1000 ≤
        Real.sqrt 2853 *
          (Real.log 2853 * (Real.log 2853 - Real.log (Real.log 2853)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (94000 : ℝ) / 1000 ≤
        Real.sqrt 2884 *
          (Real.log 2884 * (Real.log 2884 - Real.log (Real.log 2884)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (94000 : ℝ) / 1000 ≤
        Real.sqrt 2900 *
          (Real.log 2900 * (Real.log 2900 - Real.log (Real.log 2900)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)

/-- The checked batch proves the Lee–Nosal theta estimate on `[2704, 2900)`. -/
theorem theta_lee_nosal_2704_2900 {x : ℝ} (ha : 2704 ≤ x) (hb : x < 2900) :
    |Chebyshev.theta x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  exact
    lee_nosal_chain_sound Chebyshev.theta_mono Chebyshev.theta_eq_theta_coe_floor
      (by decide +kernel) batch_lower batch_upper batch_a batch_b ha hb

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
