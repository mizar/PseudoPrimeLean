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
  [⟨25757, 26184, 25744179, 26181556, 440000, 440000⟩,
    ⟨26184, 26620, 26180862, 26593978, 440000, 440000⟩,
    ⟨26620, 27031, 26593284, 27052842, 440000, 440000⟩,
    ⟨27031, 27487, 27062545, 27461106, 440000, 440000⟩,
    ⟨27487, 27910, 27470809, 27896402, 440000, 440000⟩,
    ⟨27910, 28335, 27895708, 28306052, 440000, 440000⟩,
    ⟨28335, 28745, 28305358, 28770461, 440000, 440000⟩,
    ⟨28745, 29173, 28769766, 29180804, 440000, 440000⟩,
    ⟨29173, 29587, 29190507, 29602930, 440000, 440000⟩]

/-- The kernel-checked prefix bounds for 25747. -/
private theorem psi_25747_bounds :
    (25744179 : ℝ) / 1000 ≤ Chebyshev.psi 25747 ∧ Chebyshev.psi 25747 ≤ (25744873 : ℝ) / 1000 := by
  have hl : 2 ^ 37141 ≤ Nat.lcmUpto 25747 := by decide +kernel
  have hu : Nat.lcmUpto 25747 ≤ 2 ^ (37141 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 26183. -/
private theorem psi_26183_bounds :
    (26180862 : ℝ) / 1000 ≤ Chebyshev.psi 26183 ∧ Chebyshev.psi 26183 ≤ (26181556 : ℝ) / 1000 := by
  have hl : 2 ^ 37771 ≤ Nat.lcmUpto 26183 := by decide +kernel
  have hu : Nat.lcmUpto 26183 ≤ 2 ^ (37771 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 26597. -/
private theorem psi_26597_bounds :
    (26593284 : ℝ) / 1000 ≤ Chebyshev.psi 26597 ∧ Chebyshev.psi 26597 ≤ (26593978 : ℝ) / 1000 := by
  have hl : 2 ^ 38366 ≤ Nat.lcmUpto 26597 := by decide +kernel
  have hu : Nat.lcmUpto 26597 ≤ 2 ^ (38366 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 27017. -/
private theorem psi_27017_bounds :
    (27052148 : ℝ) / 1000 ≤ Chebyshev.psi 27017 ∧ Chebyshev.psi 27017 ≤ (27052842 : ℝ) / 1000 := by
  have hl : 2 ^ 39028 ≤ Nat.lcmUpto 27017 := by decide +kernel
  have hu : Nat.lcmUpto 27017 ≤ 2 ^ (39028 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 27031. -/
private theorem psi_27031_bounds :
    (27062545 : ℝ) / 1000 ≤ Chebyshev.psi 27031 ∧ Chebyshev.psi 27031 ≤ (27063239 : ℝ) / 1000 := by
  have hl : 2 ^ 39043 ≤ Nat.lcmUpto 27031 := by decide +kernel
  have hu : Nat.lcmUpto 27031 ≤ 2 ^ (39043 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 27481. -/
private theorem psi_27481_bounds :
    (27460411 : ℝ) / 1000 ≤ Chebyshev.psi 27481 ∧ Chebyshev.psi 27481 ≤ (27461106 : ℝ) / 1000 := by
  have hl : 2 ^ 39617 ≤ Nat.lcmUpto 27481 := by decide +kernel
  have hu : Nat.lcmUpto 27481 ≤ 2 ^ (39617 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 27487. -/
private theorem psi_27487_bounds :
    (27470809 : ℝ) / 1000 ≤ Chebyshev.psi 27487 ∧ Chebyshev.psi 27487 ≤ (27471503 : ℝ) / 1000 := by
  have hl : 2 ^ 39632 ≤ Nat.lcmUpto 27487 := by decide +kernel
  have hu : Nat.lcmUpto 27487 ≤ 2 ^ (39632 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 27901. -/
private theorem psi_27901_bounds :
    (27895708 : ℝ) / 1000 ≤ Chebyshev.psi 27901 ∧ Chebyshev.psi 27901 ≤ (27896402 : ℝ) / 1000 := by
  have hl : 2 ^ 40245 ≤ Nat.lcmUpto 27901 := by decide +kernel
  have hu : Nat.lcmUpto 27901 ≤ 2 ^ (40245 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 28319. -/
private theorem psi_28319_bounds :
    (28305358 : ℝ) / 1000 ≤ Chebyshev.psi 28319 ∧ Chebyshev.psi 28319 ≤ (28306052 : ℝ) / 1000 := by
  have hl : 2 ^ 40836 ≤ Nat.lcmUpto 28319 := by decide +kernel
  have hu : Nat.lcmUpto 28319 ≤ 2 ^ (40836 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 28729. -/
private theorem psi_28729_bounds :
    (28769766 : ℝ) / 1000 ≤ Chebyshev.psi 28729 ∧ Chebyshev.psi 28729 ≤ (28770461 : ℝ) / 1000 := by
  have hl : 2 ^ 41506 ≤ Nat.lcmUpto 28729 := by decide +kernel
  have hu : Nat.lcmUpto 28729 ≤ 2 ^ (41506 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 29167. -/
private theorem psi_29167_bounds :
    (29180109 : ℝ) / 1000 ≤ Chebyshev.psi 29167 ∧ Chebyshev.psi 29167 ≤ (29180804 : ℝ) / 1000 := by
  have hl : 2 ^ 42098 ≤ Nat.lcmUpto 29167 := by decide +kernel
  have hu : Nat.lcmUpto 29167 ≤ 2 ^ (42098 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 29173. -/
private theorem psi_29173_bounds :
    (29190507 : ℝ) / 1000 ≤ Chebyshev.psi 29173 ∧ Chebyshev.psi 29173 ≤ (29191201 : ℝ) / 1000 := by
  have hl : 2 ^ 42113 ≤ Nat.lcmUpto 29173 := by decide +kernel
  have hu : Nat.lcmUpto 29173 ≤ 2 ^ (42113 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 29581. -/
private theorem psi_29581_bounds :
    (29602236 : ℝ) / 1000 ≤ Chebyshev.psi 29581 ∧ Chebyshev.psi 29581 ≤ (29602930 : ℝ) / 1000 := by
  have hl : 2 ^ 42707 ≤ Nat.lcmUpto 29581 := by decide +kernel
  have hu : Nat.lcmUpto 29581 ≤ 2 ^ (42707 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- A rational certificate bounds the envelope from 22016 onward. -/
private theorem batch_envelope {t : ℝ} (ht : 22016 ≤ t) :
    (440 : ℝ) ≤
      Real.sqrt t * (Real.log t * (Real.log t - Real.log (Real.log t)) / (8 * Real.pi)) := by
  have h :=
    lee_nosal_envelope_of_log_checks (N := 22016) (lo := 999 / 100) (hi := 10) (vlo := 230 / 100)
      (vhi := 231 / 100) (c := 440) (j := 15) (k := 4) (n := 32) (m := 32) (by norm_num only)
      (by norm_num only) (by norm_num only) (by norm_num only) (by decide +kernel)
      (by decide +kernel) (by norm_num only)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact
    h.trans
      (lee_nosal_envelope_mono (x := 22016) (y := t)
        (Real.exp_one_lt_three.le.trans (by norm_num only)) ht)

/-- Every batch cell has a checked psi lower bound. -/
private theorem batch_lower : ∀ r ∈ batchCells, (r.lo : ℝ) / 1000 ≤ Chebyshev.psi r.a := by
  intro r hr
  simp only [batchCells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change (25744179 : ℝ) / 1000 ≤ Chebyshev.psi (↑(25757 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 25747) (b := 25757) (by decide)
        (by decide +kernel)]
    exact psi_25747_bounds.1
  · change (26180862 : ℝ) / 1000 ≤ Chebyshev.psi (↑(26184 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 26183) (b := 26184) (by decide)
        (by decide +kernel)]
    exact psi_26183_bounds.1
  · change (26593284 : ℝ) / 1000 ≤ Chebyshev.psi (↑(26620 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 26597) (b := 26620) (by decide)
        (by decide +kernel)]
    exact psi_26597_bounds.1
  · change (27062545 : ℝ) / 1000 ≤ Chebyshev.psi (↑(27031 : ℕ) : ℝ)
    exact psi_27031_bounds.1
  · change (27470809 : ℝ) / 1000 ≤ Chebyshev.psi (↑(27487 : ℕ) : ℝ)
    exact psi_27487_bounds.1
  · change (27895708 : ℝ) / 1000 ≤ Chebyshev.psi (↑(27910 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 27901) (b := 27910) (by decide)
        (by decide +kernel)]
    exact psi_27901_bounds.1
  · change (28305358 : ℝ) / 1000 ≤ Chebyshev.psi (↑(28335 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 28319) (b := 28335) (by decide)
        (by decide +kernel)]
    exact psi_28319_bounds.1
  · change (28769766 : ℝ) / 1000 ≤ Chebyshev.psi (↑(28745 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 28729) (b := 28745) (by decide)
        (by decide +kernel)]
    exact psi_28729_bounds.1
  · change (29190507 : ℝ) / 1000 ≤ Chebyshev.psi (↑(29173 : ℕ) : ℝ)
    exact psi_29173_bounds.1

/-- Every batch cell has a checked psi upper bound. -/
private theorem batch_upper :
    ∀ r ∈ batchCells, Chebyshev.psi (r.b - 1 : ℕ) ≤ (r.hi : ℝ) / 1000 := by
  intro r hr
  simp only [batchCells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change Chebyshev.psi (↑(26183 : ℕ) : ℝ) ≤ (26181556 : ℝ) / 1000
    exact psi_26183_bounds.2
  · change Chebyshev.psi (↑(26619 : ℕ) : ℝ) ≤ (26593978 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 26597) (b := 26619) (by decide)
        (by decide +kernel)]
    exact psi_26597_bounds.2
  · change Chebyshev.psi (↑(27030 : ℕ) : ℝ) ≤ (27052842 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 27017) (b := 27030) (by decide)
        (by decide +kernel)]
    exact psi_27017_bounds.2
  · change Chebyshev.psi (↑(27486 : ℕ) : ℝ) ≤ (27461106 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 27481) (b := 27486) (by decide)
        (by decide +kernel)]
    exact psi_27481_bounds.2
  · change Chebyshev.psi (↑(27909 : ℕ) : ℝ) ≤ (27896402 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 27901) (b := 27909) (by decide)
        (by decide +kernel)]
    exact psi_27901_bounds.2
  · change Chebyshev.psi (↑(28334 : ℕ) : ℝ) ≤ (28306052 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 28319) (b := 28334) (by decide)
        (by decide +kernel)]
    exact psi_28319_bounds.2
  · change Chebyshev.psi (↑(28744 : ℕ) : ℝ) ≤ (28770461 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 28729) (b := 28744) (by decide)
        (by decide +kernel)]
    exact psi_28729_bounds.2
  · change Chebyshev.psi (↑(29172 : ℕ) : ℝ) ≤ (29180804 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 29167) (b := 29172) (by decide)
        (by decide +kernel)]
    exact psi_29167_bounds.2
  · change Chebyshev.psi (↑(29586 : ℕ) : ℝ) ≤ (29602930 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 29581) (b := 29586) (by decide)
        (by decide +kernel)]
    exact psi_29581_bounds.2

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
      (440000 : ℝ) / 1000 ≤
        Real.sqrt 25757 *
          (Real.log 25757 * (Real.log 25757 - Real.log (Real.log 25757)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (440000 : ℝ) / 1000 ≤
        Real.sqrt 26184 *
          (Real.log 26184 * (Real.log 26184 - Real.log (Real.log 26184)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (440000 : ℝ) / 1000 ≤
        Real.sqrt 26620 *
          (Real.log 26620 * (Real.log 26620 - Real.log (Real.log 26620)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (440000 : ℝ) / 1000 ≤
        Real.sqrt 27031 *
          (Real.log 27031 * (Real.log 27031 - Real.log (Real.log 27031)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (440000 : ℝ) / 1000 ≤
        Real.sqrt 27487 *
          (Real.log 27487 * (Real.log 27487 - Real.log (Real.log 27487)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (440000 : ℝ) / 1000 ≤
        Real.sqrt 27910 *
          (Real.log 27910 * (Real.log 27910 - Real.log (Real.log 27910)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (440000 : ℝ) / 1000 ≤
        Real.sqrt 28335 *
          (Real.log 28335 * (Real.log 28335 - Real.log (Real.log 28335)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (440000 : ℝ) / 1000 ≤
        Real.sqrt 28745 *
          (Real.log 28745 * (Real.log 28745 - Real.log (Real.log 28745)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (440000 : ℝ) / 1000 ≤
        Real.sqrt 29173 *
          (Real.log 29173 * (Real.log 29173 - Real.log (Real.log 29173)) / (8 * Real.pi))
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
      (440000 : ℝ) / 1000 ≤
        Real.sqrt 26184 *
          (Real.log 26184 * (Real.log 26184 - Real.log (Real.log 26184)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (440000 : ℝ) / 1000 ≤
        Real.sqrt 26620 *
          (Real.log 26620 * (Real.log 26620 - Real.log (Real.log 26620)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (440000 : ℝ) / 1000 ≤
        Real.sqrt 27031 *
          (Real.log 27031 * (Real.log 27031 - Real.log (Real.log 27031)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (440000 : ℝ) / 1000 ≤
        Real.sqrt 27487 *
          (Real.log 27487 * (Real.log 27487 - Real.log (Real.log 27487)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (440000 : ℝ) / 1000 ≤
        Real.sqrt 27910 *
          (Real.log 27910 * (Real.log 27910 - Real.log (Real.log 27910)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (440000 : ℝ) / 1000 ≤
        Real.sqrt 28335 *
          (Real.log 28335 * (Real.log 28335 - Real.log (Real.log 28335)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (440000 : ℝ) / 1000 ≤
        Real.sqrt 28745 *
          (Real.log 28745 * (Real.log 28745 - Real.log (Real.log 28745)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (440000 : ℝ) / 1000 ≤
        Real.sqrt 29173 *
          (Real.log 29173 * (Real.log 29173 - Real.log (Real.log 29173)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (440000 : ℝ) / 1000 ≤
        Real.sqrt 29587 *
          (Real.log 29587 * (Real.log 29587 - Real.log (Real.log 29587)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)

/-- The checked batch proves the Lee–Nosal psi estimate on `[25757, 29587)`. -/
theorem psi_lee_nosal_25757_29587 {x : ℝ} (ha : 25757 ≤ x) (hb : x < 29587) :
    |Chebyshev.psi x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  exact
    lee_nosal_chain_sound Chebyshev.psi_mono Chebyshev.psi_eq_psi_coe_floor (by decide +kernel)
      batch_lower batch_upper batch_a batch_b ha hb

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
