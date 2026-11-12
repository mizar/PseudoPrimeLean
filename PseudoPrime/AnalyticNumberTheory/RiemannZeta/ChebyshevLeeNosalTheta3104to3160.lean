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
  [⟨3104, 3126, 3020721, 3123322, 106000, 106000⟩, ⟨3126, 3152, 3046368, 3131639, 106000, 106000⟩,
    ⟨3152, 3160, 3054685, 3131639, 106000, 106000⟩]

/-- The kernel-checked prefix bounds for 3089. -/
private theorem psi_3089_bounds :
    (3096981 : ℝ) / 1000 ≤ Chebyshev.psi 3089 ∧ Chebyshev.psi 3089 ≤ (3097675 : ℝ) / 1000 := by
  have hl : 2 ^ 4468 ≤ Nat.lcmUpto 3089 := by decide +kernel
  have hu : Nat.lcmUpto 3089 ≤ 2 ^ (4468 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 3125. -/
private theorem psi_3125_bounds :
    (3122628 : ℝ) / 1000 ≤ Chebyshev.psi 3125 ∧ Chebyshev.psi 3125 ≤ (3123322 : ℝ) / 1000 := by
  have hl : 2 ^ 4505 ≤ Nat.lcmUpto 3125 := by decide +kernel
  have hu : Nat.lcmUpto 3125 ≤ 2 ^ (4505 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 3137. -/
private theorem psi_3137_bounds :
    (3130945 : ℝ) / 1000 ≤ Chebyshev.psi 3137 ∧ Chebyshev.psi 3137 ≤ (3131639 : ℝ) / 1000 := by
  have hl : 2 ^ 4517 ≤ Nat.lcmUpto 3137 := by decide +kernel
  have hu : Nat.lcmUpto 3137 ≤ 2 ^ (4517 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- A rational certificate bounds the envelope from 3104 onward. -/
private theorem batch_envelope {t : ℝ} (ht : 3104 ≤ t) :
    (106 : ℝ) ≤
      Real.sqrt t * (Real.log t * (Real.log t - Real.log (Real.log t)) / (8 * Real.pi)) := by
  have h :=
    lee_nosal_envelope_of_log_checks (N := 3104) (lo := 804 / 100) (hi := 805 / 100) (vlo :=
      208 / 100) (vhi := 209 / 100) (c := 106) (j := 12) (k := 4) (n := 32) (m := 32)
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by decide +kernel) (by decide +kernel) (by norm_num only)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact
    h.trans
      (lee_nosal_envelope_mono (x := 3104) (y := t)
        (Real.exp_one_lt_three.le.trans (by norm_num only)) ht)

/-- Every batch cell has a checked theta lower bound. -/
private theorem batch_lower : ∀ r ∈ batchCells, (r.lo : ℝ) / 1000 ≤ Chebyshev.theta r.a := by
  intro r hr
  simp only [batchCells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · change (3020721 : ℝ) / 1000 ≤ Chebyshev.theta (↑(3104 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_7626 (x := 3104) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3089) (b := 3104) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3089_bounds.1]
  · change (3046368 : ℝ) / 1000 ≤ Chebyshev.theta (↑(3126 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_7626 (x := 3126) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3125) (b := 3126) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3125_bounds.1]
  · change (3054685 : ℝ) / 1000 ≤ Chebyshev.theta (↑(3152 : ℕ) : ℝ)
    have hd := Arithmetic.psi_sub_theta_le_7626 (x := 3152) (by norm_num only) (by norm_num only)
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3137) (b := 3152) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3137_bounds.1]

/-- Every batch cell has a checked theta upper bound. -/
private theorem batch_upper :
    ∀ r ∈ batchCells, Chebyshev.theta (r.b - 1 : ℕ) ≤ (r.hi : ℝ) / 1000 := by
  intro r hr
  simp only [batchCells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · change Chebyshev.theta (↑(3125 : ℕ) : ℝ) ≤ (3123322 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 3125
    linarith only [hd, psi_3125_bounds.2]
  · change Chebyshev.theta (↑(3151 : ℕ) : ℝ) ≤ (3131639 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 3151
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3137) (b := 3151) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3137_bounds.2]
  · change Chebyshev.theta (↑(3159 : ℕ) : ℝ) ≤ (3131639 : ℝ) / 1000
    have hd := Chebyshev.theta_le_psi 3159
    have he :=
      Arithmetic.psi_eq_of_no_prime_power (a := 3137) (b := 3159) (by decide) (by decide +kernel)
    norm_num only [Nat.cast_ofNat] at he ⊢
    linarith only [hd, he, psi_3137_bounds.2]

/-- The envelope bound applies at every cell a endpoint. -/
private theorem batch_a :
    ∀ r ∈ batchCells,
      (r.ca : ℝ) / 1000 ≤
        Real.sqrt r.a *
          (Real.log r.a * (Real.log r.a - Real.log (Real.log r.a)) / (8 * Real.pi)) := by
  intro r hr
  simp only [batchCells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · change
      (106000 : ℝ) / 1000 ≤
        Real.sqrt 3104 *
          (Real.log 3104 * (Real.log 3104 - Real.log (Real.log 3104)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (106000 : ℝ) / 1000 ≤
        Real.sqrt 3126 *
          (Real.log 3126 * (Real.log 3126 - Real.log (Real.log 3126)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (106000 : ℝ) / 1000 ≤
        Real.sqrt 3152 *
          (Real.log 3152 * (Real.log 3152 - Real.log (Real.log 3152)) / (8 * Real.pi))
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
  rcases hr with rfl | rfl | rfl
  · change
      (106000 : ℝ) / 1000 ≤
        Real.sqrt 3126 *
          (Real.log 3126 * (Real.log 3126 - Real.log (Real.log 3126)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (106000 : ℝ) / 1000 ≤
        Real.sqrt 3152 *
          (Real.log 3152 * (Real.log 3152 - Real.log (Real.log 3152)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (106000 : ℝ) / 1000 ≤
        Real.sqrt 3160 *
          (Real.log 3160 * (Real.log 3160 - Real.log (Real.log 3160)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)

/-- The checked batch proves the Lee–Nosal theta estimate on `[3104, 3160)`. -/
theorem theta_lee_nosal_3104_3160 {x : ℝ} (ha : 3104 ≤ x) (hb : x < 3160) :
    |Chebyshev.theta x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  exact
    lee_nosal_chain_sound Chebyshev.theta_mono Chebyshev.theta_eq_theta_coe_floor
      (by decide +kernel) batch_lower batch_upper batch_a batch_b ha hb

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
