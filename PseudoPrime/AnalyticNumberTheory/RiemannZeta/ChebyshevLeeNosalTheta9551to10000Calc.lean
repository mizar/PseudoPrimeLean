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
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalEnvelope7776
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalMonotone
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalChecker

/-! # Batch certificate for Lee–Nosal theta cells -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The local cells store endpoint bounds in thousandths. -/
def theta9551Cells : List LeeNosalCell :=
  [⟨9551, 9643, 9432324, 9655541, 211000, 211000⟩, ⟨9643, 9716, 9505797, 9719310, 211000, 211000⟩,
    ⟨9716, 9771, 9560556, 9792784, 211000, 211000⟩, ⟨9771, 9845, 9634030, 9875962, 211000, 211000⟩,
    ⟨9845, 9928, 9717207, 9958446, 211000, 211000⟩,
    ⟨9928, 10000, 9799692, 10013898, 211000, 211000⟩]

/-- The kernel-checked prefix bounds for 9551. -/
theorem theta9551_psi_9551_bounds :
    (9590384 : ℝ) / 1000 ≤ Chebyshev.psi 9551 ∧ Chebyshev.psi 9551 ≤ (9591078 : ℝ) / 1000 := by
  have hl : 2 ^ 13836 ≤ Nat.lcmUpto 9551 := by decide +kernel
  have hu : Nat.lcmUpto 9551 ≤ 2 ^ (13836 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 9631. -/
theorem theta9551_psi_9631_bounds :
    (9654847 : ℝ) / 1000 ≤ Chebyshev.psi 9631 ∧ Chebyshev.psi 9631 ≤ (9655541 : ℝ) / 1000 := by
  have hl : 2 ^ 13929 ≤ Nat.lcmUpto 9631 := by decide +kernel
  have hu : Nat.lcmUpto 9631 ≤ 2 ^ (13929 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 9643. -/
theorem theta9551_psi_9643_bounds :
    (9663857 : ℝ) / 1000 ≤ Chebyshev.psi 9643 ∧ Chebyshev.psi 9643 ≤ (9664552 : ℝ) / 1000 := by
  have hl : 2 ^ 13942 ≤ Nat.lcmUpto 9643 := by decide +kernel
  have hu : Nat.lcmUpto 9643 ≤ 2 ^ (13942 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 9697. -/
theorem theta9551_psi_9697_bounds :
    (9718616 : ℝ) / 1000 ≤ Chebyshev.psi 9697 ∧ Chebyshev.psi 9697 ≤ (9719310 : ℝ) / 1000 := by
  have hl : 2 ^ 14021 ≤ Nat.lcmUpto 9697 := by decide +kernel
  have hu : Nat.lcmUpto 9697 ≤ 2 ^ (14021 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 9769. -/
theorem theta9551_psi_9769_bounds :
    (9792090 : ℝ) / 1000 ≤ Chebyshev.psi 9769 ∧ Chebyshev.psi 9769 ≤ (9792784 : ℝ) / 1000 := by
  have hl : 2 ^ 14127 ≤ Nat.lcmUpto 9769 := by decide +kernel
  have hu : Nat.lcmUpto 9769 ≤ 2 ^ (14127 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 9839. -/
theorem theta9551_psi_9839_bounds :
    (9875267 : ℝ) / 1000 ≤ Chebyshev.psi 9839 ∧ Chebyshev.psi 9839 ≤ (9875962 : ℝ) / 1000 := by
  have hl : 2 ^ 14247 ≤ Nat.lcmUpto 9839 := by decide +kernel
  have hu : Nat.lcmUpto 9839 ≤ 2 ^ (14247 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 9923. -/
theorem theta9551_psi_9923_bounds :
    (9957752 : ℝ) / 1000 ≤ Chebyshev.psi 9923 ∧ Chebyshev.psi 9923 ≤ (9958446 : ℝ) / 1000 := by
  have hl : 2 ^ 14366 ≤ Nat.lcmUpto 9923 := by decide +kernel
  have hu : Nat.lcmUpto 9923 ≤ 2 ^ (14366 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 9973. -/
theorem theta9551_psi_9973_bounds :
    (10013204 : ℝ) / 1000 ≤ Chebyshev.psi 9973 ∧ Chebyshev.psi 9973 ≤ (10013898 : ℝ) / 1000 := by
  have hl : 2 ^ 14446 ≤ Nat.lcmUpto 9973 := by decide +kernel
  have hu : Nat.lcmUpto 9973 ≤ 2 ^ (14446 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- Every batch cell has a checked theta lower bound. -/
theorem theta9551_lower : ∀ r ∈ theta9551Cells, (r.lo : ℝ) / 1000 ≤ Chebyshev.theta r.a := by
  intro r hr
  simp only [theta9551Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · change (9432324 : ℝ) / 1000 ≤ Chebyshev.theta (↑(9551 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 9551) (by norm_num only) (by norm_num only)
    linarith only [hd, theta9551_psi_9551_bounds.1]
  · change (9505797 : ℝ) / 1000 ≤ Chebyshev.theta (↑(9643 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 9643) (by norm_num only) (by norm_num only)
    linarith only [hd, theta9551_psi_9643_bounds.1]
  · change (9560556 : ℝ) / 1000 ≤ Chebyshev.theta (↑(9716 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 9716) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 9697) (b := 9716) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta9551_psi_9697_bounds.1]
  · change (9634030 : ℝ) / 1000 ≤ Chebyshev.theta (↑(9771 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 9771) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 9769) (b := 9771) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta9551_psi_9769_bounds.1]
  · change (9717207 : ℝ) / 1000 ≤ Chebyshev.theta (↑(9845 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 9845) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 9839) (b := 9845) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta9551_psi_9839_bounds.1]
  · change (9799692 : ℝ) / 1000 ≤ Chebyshev.theta (↑(9928 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_15806 (x := 9928) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 9923) (b := 9928) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta9551_psi_9923_bounds.1]

/-- Every batch cell has a checked theta upper bound. -/
theorem theta9551_upper :
    ∀ r ∈ theta9551Cells, Chebyshev.theta (r.b - 1 : ℕ) ≤ (r.hi : ℝ) / 1000 := by
  intro r hr
  simp only [theta9551Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · change Chebyshev.theta (↑(9642 : ℕ) : ℝ) ≤ (9655541 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 9642
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 9631) (b := 9642) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta9551_psi_9631_bounds.2]
  · change Chebyshev.theta (↑(9715 : ℕ) : ℝ) ≤ (9719310 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 9715
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 9697) (b := 9715) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta9551_psi_9697_bounds.2]
  · change Chebyshev.theta (↑(9770 : ℕ) : ℝ) ≤ (9792784 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 9770
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 9769) (b := 9770) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta9551_psi_9769_bounds.2]
  · change Chebyshev.theta (↑(9844 : ℕ) : ℝ) ≤ (9875962 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 9844
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 9839) (b := 9844) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta9551_psi_9839_bounds.2]
  · change Chebyshev.theta (↑(9927 : ℕ) : ℝ) ≤ (9958446 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 9927
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 9923) (b := 9927) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta9551_psi_9923_bounds.2]
  · change Chebyshev.theta (↑(9999 : ℕ) : ℝ) ≤ (10013898 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 9999
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 9973) (b := 9999) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, theta9551_psi_9973_bounds.2]

/-- The envelope bound applies at every cell a endpoint. -/
theorem theta9551_a :
    ∀ r ∈ theta9551Cells,
      (r.ca : ℝ) / 1000 ≤
        Real.sqrt r.a *
          (Real.log r.a * (Real.log r.a - Real.log (Real.log r.a)) / (8 * Real.pi)) := by
  intro r hr
  simp only [theta9551Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 9551 *
          (Real.log 9551 * (Real.log 9551 - Real.log (Real.log 9551)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 9643 *
          (Real.log 9643 * (Real.log 9643 - Real.log (Real.log 9643)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 9716 *
          (Real.log 9716 * (Real.log 9716 - Real.log (Real.log 9716)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 9771 *
          (Real.log 9771 * (Real.log 9771 - Real.log (Real.log 9771)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 9845 *
          (Real.log 9845 * (Real.log 9845 - Real.log (Real.log 9845)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 9928 *
          (Real.log 9928 * (Real.log 9928 - Real.log (Real.log 9928)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)

/-- The envelope bound applies at every cell b endpoint. -/
theorem theta9551_b :
    ∀ r ∈ theta9551Cells,
      (r.cb : ℝ) / 1000 ≤
        Real.sqrt r.b *
          (Real.log r.b * (Real.log r.b - Real.log (Real.log r.b)) / (8 * Real.pi)) := by
  intro r hr
  simp only [theta9551Cells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 9643 *
          (Real.log 9643 * (Real.log 9643 - Real.log (Real.log 9643)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 9716 *
          (Real.log 9716 * (Real.log 9716 - Real.log (Real.log 9716)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 9771 *
          (Real.log 9771 * (Real.log 9771 - Real.log (Real.log 9771)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 9845 *
          (Real.log 9845 * (Real.log 9845 - Real.log (Real.log 9845)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 9928 *
          (Real.log 9928 * (Real.log 9928 - Real.log (Real.log 9928)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)
  · change
      (211000 : ℝ) / 1000 ≤
        Real.sqrt 10000 *
          (Real.log 10000 * (Real.log 10000 - Real.log (Real.log 10000)) / (8 * Real.pi))
    norm_num only
    exact lee_nosal_envelope_ge_211 (by norm_num only)

/-- The cells form a checked chain covering `[9551, 10000)`. -/
theorem theta9551_check : leeNosalChainCheck 9551 10000 theta9551Cells = true := by decide +kernel

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
