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
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSmallDefect
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalLogCheck
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalMonotone
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalChecker

/-! # Batch certificate for Lee–Nosal theta cells -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The local cells store endpoint bounds in thousandths. -/
private def batchCells : List LeeNosalCell :=
  [⟨2667, 2675, 2581219, 2656140, 94000, 94000⟩, ⟨2675, 2683, 2589536, 2663765, 94000, 94000⟩,
    ⟨2683, 2698, 2604786, 2695650, 94000, 94000⟩, ⟨2698, 2704, 2629046, 2703275, 94000, 94000⟩]

/-- The kernel-checked prefix bounds for 2663. -/
private theorem psi_2663_bounds :
    (2647129 : ℝ) / 1000 ≤ Chebyshev.psi 2663 ∧ Chebyshev.psi 2663 ≤ (2647823 : ℝ) / 1000 := by
  have hl : 2 ^ 3819 ≤ Nat.lcmUpto 2663 := by decide +kernel
  have hu : Nat.lcmUpto 2663 ≤ 2 ^ (3819 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 2671. -/
private theorem psi_2671_bounds :
    (2655446 : ℝ) / 1000 ≤ Chebyshev.psi 2671 ∧ Chebyshev.psi 2671 ≤ (2656140 : ℝ) / 1000 := by
  have hl : 2 ^ 3831 ≤ Nat.lcmUpto 2671 := by decide +kernel
  have hu : Nat.lcmUpto 2671 ≤ 2 ^ (3831 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 2677. -/
private theorem psi_2677_bounds :
    (2663071 : ℝ) / 1000 ≤ Chebyshev.psi 2677 ∧ Chebyshev.psi 2677 ≤ (2663765 : ℝ) / 1000 := by
  have hl : 2 ^ 3842 ≤ Nat.lcmUpto 2677 := by decide +kernel
  have hu : Nat.lcmUpto 2677 ≤ 2 ^ (3842 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 2683. -/
private theorem psi_2683_bounds :
    (2670696 : ℝ) / 1000 ≤ Chebyshev.psi 2683 ∧ Chebyshev.psi 2683 ≤ (2671390 : ℝ) / 1000 := by
  have hl : 2 ^ 3853 ≤ Nat.lcmUpto 2683 := by decide +kernel
  have hu : Nat.lcmUpto 2683 ≤ 2 ^ (3853 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 2693. -/
private theorem psi_2693_bounds :
    (2694956 : ℝ) / 1000 ≤ Chebyshev.psi 2693 ∧ Chebyshev.psi 2693 ≤ (2695650 : ℝ) / 1000 := by
  have hl : 2 ^ 3888 ≤ Nat.lcmUpto 2693 := by decide +kernel
  have hu : Nat.lcmUpto 2693 ≤ 2 ^ (3888 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 2699. -/
private theorem psi_2699_bounds :
    (2702580 : ℝ) / 1000 ≤ Chebyshev.psi 2699 ∧ Chebyshev.psi 2699 ≤ (2703275 : ℝ) / 1000 := by
  have hl : 2 ^ 3899 ≤ Nat.lcmUpto 2699 := by decide +kernel
  have hu : Nat.lcmUpto 2699 ≤ 2 ^ (3899 + 1) := by decide +kernel
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
  rcases hr with rfl | rfl | rfl | rfl
  · change (2581219 : ℝ) / 1000 ≤ Chebyshev.theta (↑(2667 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_6591 (x := 2667) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 2663) (b := 2667) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_2663_bounds.1]
  · change (2589536 : ℝ) / 1000 ≤ Chebyshev.theta (↑(2675 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_6591 (x := 2675) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 2671) (b := 2675) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_2671_bounds.1]
  · change (2604786 : ℝ) / 1000 ≤ Chebyshev.theta (↑(2683 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_6591 (x := 2683) (by norm_num only) (by norm_num only)
    linarith only [hd, psi_2683_bounds.1]
  · change (2629046 : ℝ) / 1000 ≤ Chebyshev.theta (↑(2698 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_6591 (x := 2698) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 2693) (b := 2698) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_2693_bounds.1]

/-- Every batch cell has a checked theta upper bound. -/
private theorem batch_upper :
    ∀ r ∈ batchCells, Chebyshev.theta (r.b - 1 : ℕ) ≤ (r.hi : ℝ) / 1000 := by
  intro r hr
  simp only [batchCells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · change Chebyshev.theta (↑(2674 : ℕ) : ℝ) ≤ (2656140 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 2674
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 2671) (b := 2674) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_2671_bounds.2]
  · change Chebyshev.theta (↑(2682 : ℕ) : ℝ) ≤ (2663765 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 2682
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 2677) (b := 2682) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_2677_bounds.2]
  · change Chebyshev.theta (↑(2697 : ℕ) : ℝ) ≤ (2695650 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 2697
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 2693) (b := 2697) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_2693_bounds.2]
  · change Chebyshev.theta (↑(2703 : ℕ) : ℝ) ≤ (2703275 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 2703
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 2699) (b := 2703) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_2699_bounds.2]

/-- The envelope bound applies at every cell a endpoint. -/
private theorem batch_a :
    ∀ r ∈ batchCells,
      (r.ca : ℝ) / 1000 ≤
        Real.sqrt r.a *
          (Real.log r.a * (Real.log r.a - Real.log (Real.log r.a)) / (8 * Real.pi)) := by
  intro r hr
  simp only [batchCells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · change
      (94000 : ℝ) / 1000 ≤
        Real.sqrt 2667 *
          (Real.log 2667 * (Real.log 2667 - Real.log (Real.log 2667)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (94000 : ℝ) / 1000 ≤
        Real.sqrt 2675 *
          (Real.log 2675 * (Real.log 2675 - Real.log (Real.log 2675)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (94000 : ℝ) / 1000 ≤
        Real.sqrt 2683 *
          (Real.log 2683 * (Real.log 2683 - Real.log (Real.log 2683)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (94000 : ℝ) / 1000 ≤
        Real.sqrt 2698 *
          (Real.log 2698 * (Real.log 2698 - Real.log (Real.log 2698)) / (8 * Real.pi))
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
  rcases hr with rfl | rfl | rfl | rfl
  · change
      (94000 : ℝ) / 1000 ≤
        Real.sqrt 2675 *
          (Real.log 2675 * (Real.log 2675 - Real.log (Real.log 2675)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (94000 : ℝ) / 1000 ≤
        Real.sqrt 2683 *
          (Real.log 2683 * (Real.log 2683 - Real.log (Real.log 2683)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (94000 : ℝ) / 1000 ≤
        Real.sqrt 2698 *
          (Real.log 2698 * (Real.log 2698 - Real.log (Real.log 2698)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (94000 : ℝ) / 1000 ≤
        Real.sqrt 2704 *
          (Real.log 2704 * (Real.log 2704 - Real.log (Real.log 2704)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)

/-- The checked batch proves the Lee–Nosal theta estimate on `[2667, 2704)`. -/
theorem theta_lee_nosal_2667_2704 {x : ℝ} (ha : 2667 ≤ x) (hb : x < 2704) :
    |Chebyshev.theta x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  exact
    lee_nosal_chain_sound Chebyshev.theta_mono Chebyshev.theta_eq_theta_coe_floor
      (by decide +kernel) batch_lower batch_upper batch_a batch_b ha hb

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
