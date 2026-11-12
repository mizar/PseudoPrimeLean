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
  [⟨3479, 3501, 3387723, 3484451, 114000, 114000⟩, ⟨3501, 3522, 3408517, 3500394, 114000, 114000⟩,
    ⟨3522, 3538, 3424460, 3525347, 114000, 114000⟩, ⟨3538, 3563, 3449413, 3566243, 114000, 114000⟩,
    ⟨3563, 3600, 3490309, 3598821, 114000, 114000⟩]

/-- The kernel-checked prefix bounds for 3469. -/
private theorem psi_3469_bounds :
    (3462963 : ℝ) / 1000 ≤ Chebyshev.psi 3469 ∧ Chebyshev.psi 3469 ≤ (3463657 : ℝ) / 1000 := by
  have hl : 2 ^ 4996 ≤ Nat.lcmUpto 3469 := by decide +kernel
  have hu : Nat.lcmUpto 3469 ≤ 2 ^ (4996 + 1) := by decide +kernel
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

/-- The kernel-checked prefix bounds for 3517. -/
private theorem psi_3517_bounds :
    (3499700 : ℝ) / 1000 ≤ Chebyshev.psi 3517 ∧ Chebyshev.psi 3517 ≤ (3500394 : ℝ) / 1000 := by
  have hl : 2 ^ 5049 ≤ Nat.lcmUpto 3517 := by decide +kernel
  have hu : Nat.lcmUpto 3517 ≤ 2 ^ (5049 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 3533. -/
private theorem psi_3533_bounds :
    (3524653 : ℝ) / 1000 ≤ Chebyshev.psi 3533 ∧ Chebyshev.psi 3533 ≤ (3525347 : ℝ) / 1000 := by
  have hl : 2 ^ 5085 ≤ Nat.lcmUpto 3533 := by decide +kernel
  have hu : Nat.lcmUpto 3533 ≤ 2 ^ (5085 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 3559. -/
private theorem psi_3559_bounds :
    (3565549 : ℝ) / 1000 ≤ Chebyshev.psi 3559 ∧ Chebyshev.psi 3559 ≤ (3566243 : ℝ) / 1000 := by
  have hl : 2 ^ 5144 ≤ Nat.lcmUpto 3559 := by decide +kernel
  have hu : Nat.lcmUpto 3559 ≤ 2 ^ (5144 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 3593. -/
private theorem psi_3593_bounds :
    (3598127 : ℝ) / 1000 ≤ Chebyshev.psi 3593 ∧ Chebyshev.psi 3593 ≤ (3598821 : ℝ) / 1000 := by
  have hl : 2 ^ 5191 ≤ Nat.lcmUpto 3593 := by decide +kernel
  have hu : Nat.lcmUpto 3593 ≤ 2 ^ (5191 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- A rational certificate bounds the envelope from 3479 onward. -/
private theorem batch_envelope {t : ℝ} (ht : 3479 ≤ t) :
    (114 : ℝ) ≤
      Real.sqrt t * (Real.log t * (Real.log t - Real.log (Real.log t)) / (8 * Real.pi)) := by
  have h :=
    lee_nosal_envelope_of_log_checks (N := 3479) (lo := 815 / 100) (hi := 816 / 100) (vlo :=
      209 / 100) (vhi := 210 / 100) (c := 114) (j := 12) (k := 4) (n := 32) (m := 32)
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by decide +kernel) (by decide +kernel) (by norm_num only)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact
    h.trans
      (lee_nosal_envelope_mono (x := 3479) (y := t)
        (Real.exp_one_lt_three.le.trans (by norm_num only)) ht)

/-- Every batch cell has a checked theta lower bound. -/
private theorem batch_lower : ∀ r ∈ batchCells, (r.lo : ℝ) / 1000 ≤ Chebyshev.theta r.a := by
  intro r hr
  simp only [batchCells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · change (3387723 : ℝ) / 1000 ≤ Chebyshev.theta (↑(3479 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_7524 (x := 3479) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3469) (b := 3479) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3469_bounds.1]
  · change (3408517 : ℝ) / 1000 ≤ Chebyshev.theta (↑(3501 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_7524 (x := 3501) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3499) (b := 3501) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3499_bounds.1]
  · change (3424460 : ℝ) / 1000 ≤ Chebyshev.theta (↑(3522 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_7524 (x := 3522) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3517) (b := 3522) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3517_bounds.1]
  · change (3449413 : ℝ) / 1000 ≤ Chebyshev.theta (↑(3538 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_7524 (x := 3538) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3533) (b := 3538) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3533_bounds.1]
  · change (3490309 : ℝ) / 1000 ≤ Chebyshev.theta (↑(3563 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_7524 (x := 3563) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3559) (b := 3563) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3559_bounds.1]

/-- Every batch cell has a checked theta upper bound. -/
private theorem batch_upper :
    ∀ r ∈ batchCells, Chebyshev.theta (r.b - 1 : ℕ) ≤ (r.hi : ℝ) / 1000 := by
  intro r hr
  simp only [batchCells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · change Chebyshev.theta (↑(3500 : ℕ) : ℝ) ≤ (3484451 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 3500
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3499) (b := 3500) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3499_bounds.2]
  · change Chebyshev.theta (↑(3521 : ℕ) : ℝ) ≤ (3500394 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 3521
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3517) (b := 3521) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3517_bounds.2]
  · change Chebyshev.theta (↑(3537 : ℕ) : ℝ) ≤ (3525347 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 3537
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3533) (b := 3537) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3533_bounds.2]
  · change Chebyshev.theta (↑(3562 : ℕ) : ℝ) ≤ (3566243 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 3562
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3559) (b := 3562) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3559_bounds.2]
  · change Chebyshev.theta (↑(3599 : ℕ) : ℝ) ≤ (3598821 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 3599
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3593) (b := 3599) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3593_bounds.2]

/-- The envelope bound applies at every cell a endpoint. -/
private theorem batch_a :
    ∀ r ∈ batchCells,
      (r.ca : ℝ) / 1000 ≤
        Real.sqrt r.a *
          (Real.log r.a * (Real.log r.a - Real.log (Real.log r.a)) / (8 * Real.pi)) := by
  intro r hr
  simp only [batchCells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · change
      (114000 : ℝ) / 1000 ≤
        Real.sqrt 3479 *
          (Real.log 3479 * (Real.log 3479 - Real.log (Real.log 3479)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (114000 : ℝ) / 1000 ≤
        Real.sqrt 3501 *
          (Real.log 3501 * (Real.log 3501 - Real.log (Real.log 3501)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (114000 : ℝ) / 1000 ≤
        Real.sqrt 3522 *
          (Real.log 3522 * (Real.log 3522 - Real.log (Real.log 3522)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (114000 : ℝ) / 1000 ≤
        Real.sqrt 3538 *
          (Real.log 3538 * (Real.log 3538 - Real.log (Real.log 3538)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (114000 : ℝ) / 1000 ≤
        Real.sqrt 3563 *
          (Real.log 3563 * (Real.log 3563 - Real.log (Real.log 3563)) / (8 * Real.pi))
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
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · change
      (114000 : ℝ) / 1000 ≤
        Real.sqrt 3501 *
          (Real.log 3501 * (Real.log 3501 - Real.log (Real.log 3501)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (114000 : ℝ) / 1000 ≤
        Real.sqrt 3522 *
          (Real.log 3522 * (Real.log 3522 - Real.log (Real.log 3522)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (114000 : ℝ) / 1000 ≤
        Real.sqrt 3538 *
          (Real.log 3538 * (Real.log 3538 - Real.log (Real.log 3538)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (114000 : ℝ) / 1000 ≤
        Real.sqrt 3563 *
          (Real.log 3563 * (Real.log 3563 - Real.log (Real.log 3563)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (114000 : ℝ) / 1000 ≤
        Real.sqrt 3600 *
          (Real.log 3600 * (Real.log 3600 - Real.log (Real.log 3600)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)

/-- The checked batch proves the Lee–Nosal theta estimate on `[3479, 3600)`. -/
theorem theta_lee_nosal_3479_3600 {x : ℝ} (ha : 3479 ≤ x) (hb : x < 3600) :
    |Chebyshev.theta x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  exact
    lee_nosal_chain_sound Chebyshev.theta_mono Chebyshev.theta_eq_theta_coe_floor
      (by decide +kernel) batch_lower batch_upper batch_a batch_b ha hb

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
