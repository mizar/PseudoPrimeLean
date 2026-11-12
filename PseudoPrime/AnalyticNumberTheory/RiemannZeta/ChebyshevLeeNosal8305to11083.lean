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
  [⟨8305, 8518, 8303210, 8475111, 215000, 215000⟩, ⟨8518, 8689, 8474417, 8656716, 215000, 215000⟩,
    ⟨8689, 8880, 8665032, 8883375, 215000, 215000⟩, ⟨8880, 9097, 8882681, 9083694, 215000, 215000⟩,
    ⟨9097, 9298, 9083000, 9293718, 215000, 215000⟩, ⟨9298, 9479, 9293024, 9508594, 215000, 215000⟩,
    ⟨9479, 9679, 9516910, 9692278, 215000, 215000⟩, ⟨9679, 9859, 9700594, 9893983, 215000, 215000⟩,
    ⟨9859, 10069, 9902300, 10069350, 215000, 215000⟩,
    ⟨10069, 10259, 10077666, 10276601, 215000, 215000⟩,
    ⟨10259, 10457, 10284917, 10470682, 215000, 215000⟩,
    ⟨10457, 10657, 10478999, 10669615, 215000, 215000⟩,
    ⟨10657, 10861, 10678625, 10865083, 215000, 215000⟩,
    ⟨10861, 11083, 10873399, 11069561, 215000, 215000⟩]

/-- The kernel-checked prefix bounds for 8297. -/
private theorem psi_8297_bounds :
    (8303210 : ℝ) / 1000 ≤ Chebyshev.psi 8297 ∧ Chebyshev.psi 8297 ≤ (8303904 : ℝ) / 1000 := by
  have hl : 2 ^ 11979 ≤ Nat.lcmUpto 8297 := by decide +kernel
  have hu : Nat.lcmUpto 8297 ≤ 2 ^ (11979 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 8513. -/
private theorem psi_8513_bounds :
    (8474417 : ℝ) / 1000 ≤ Chebyshev.psi 8513 ∧ Chebyshev.psi 8513 ≤ (8475111 : ℝ) / 1000 := by
  have hl : 2 ^ 12226 ≤ Nat.lcmUpto 8513 := by decide +kernel
  have hu : Nat.lcmUpto 8513 ≤ 2 ^ (12226 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 8681. -/
private theorem psi_8681_bounds :
    (8656021 : ℝ) / 1000 ≤ Chebyshev.psi 8681 ∧ Chebyshev.psi 8681 ≤ (8656716 : ℝ) / 1000 := by
  have hl : 2 ^ 12488 ≤ Nat.lcmUpto 8681 := by decide +kernel
  have hu : Nat.lcmUpto 8681 ≤ 2 ^ (12488 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 8689. -/
private theorem psi_8689_bounds :
    (8665032 : ℝ) / 1000 ≤ Chebyshev.psi 8689 ∧ Chebyshev.psi 8689 ≤ (8665727 : ℝ) / 1000 := by
  have hl : 2 ^ 12501 ≤ Nat.lcmUpto 8689 := by decide +kernel
  have hu : Nat.lcmUpto 8689 ≤ 2 ^ (12501 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 8867. -/
private theorem psi_8867_bounds :
    (8882681 : ℝ) / 1000 ≤ Chebyshev.psi 8867 ∧ Chebyshev.psi 8867 ≤ (8883375 : ℝ) / 1000 := by
  have hl : 2 ^ 12815 ≤ Nat.lcmUpto 8867 := by decide +kernel
  have hu : Nat.lcmUpto 8867 ≤ 2 ^ (12815 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 9091. -/
private theorem psi_9091_bounds :
    (9083000 : ℝ) / 1000 ≤ Chebyshev.psi 9091 ∧ Chebyshev.psi 9091 ≤ (9083694 : ℝ) / 1000 := by
  have hl : 2 ^ 13104 ≤ Nat.lcmUpto 9091 := by decide +kernel
  have hu : Nat.lcmUpto 9091 ≤ 2 ^ (13104 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 9293. -/
private theorem psi_9293_bounds :
    (9293024 : ℝ) / 1000 ≤ Chebyshev.psi 9293 ∧ Chebyshev.psi 9293 ≤ (9293718 : ℝ) / 1000 := by
  have hl : 2 ^ 13407 ≤ Nat.lcmUpto 9293 := by decide +kernel
  have hu : Nat.lcmUpto 9293 ≤ 2 ^ (13407 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 9473. -/
private theorem psi_9473_bounds :
    (9507899 : ℝ) / 1000 ≤ Chebyshev.psi 9473 ∧ Chebyshev.psi 9473 ≤ (9508594 : ℝ) / 1000 := by
  have hl : 2 ^ 13717 ≤ Nat.lcmUpto 9473 := by decide +kernel
  have hu : Nat.lcmUpto 9473 ≤ 2 ^ (13717 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 9479. -/
private theorem psi_9479_bounds :
    (9516910 : ℝ) / 1000 ≤ Chebyshev.psi 9479 ∧ Chebyshev.psi 9479 ≤ (9517604 : ℝ) / 1000 := by
  have hl : 2 ^ 13730 ≤ Nat.lcmUpto 9479 := by decide +kernel
  have hu : Nat.lcmUpto 9479 ≤ 2 ^ (13730 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 9677. -/
private theorem psi_9677_bounds :
    (9691583 : ℝ) / 1000 ≤ Chebyshev.psi 9677 ∧ Chebyshev.psi 9677 ≤ (9692278 : ℝ) / 1000 := by
  have hl : 2 ^ 13982 ≤ Nat.lcmUpto 9677 := by decide +kernel
  have hu : Nat.lcmUpto 9677 ≤ 2 ^ (13982 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 9679. -/
private theorem psi_9679_bounds :
    (9700594 : ℝ) / 1000 ≤ Chebyshev.psi 9679 ∧ Chebyshev.psi 9679 ≤ (9701288 : ℝ) / 1000 := by
  have hl : 2 ^ 13995 ≤ Nat.lcmUpto 9679 := by decide +kernel
  have hu : Nat.lcmUpto 9679 ≤ 2 ^ (13995 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 9857. -/
private theorem psi_9857_bounds :
    (9893289 : ℝ) / 1000 ≤ Chebyshev.psi 9857 ∧ Chebyshev.psi 9857 ≤ (9893983 : ℝ) / 1000 := by
  have hl : 2 ^ 14273 ≤ Nat.lcmUpto 9857 := by decide +kernel
  have hu : Nat.lcmUpto 9857 ≤ 2 ^ (14273 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 9859. -/
private theorem psi_9859_bounds :
    (9902300 : ℝ) / 1000 ≤ Chebyshev.psi 9859 ∧ Chebyshev.psi 9859 ≤ (9902994 : ℝ) / 1000 := by
  have hl : 2 ^ 14286 ≤ Nat.lcmUpto 9859 := by decide +kernel
  have hu : Nat.lcmUpto 9859 ≤ 2 ^ (14286 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 10067. -/
private theorem psi_10067_bounds :
    (10068655 : ℝ) / 1000 ≤ Chebyshev.psi 10067 ∧ Chebyshev.psi 10067 ≤ (10069350 : ℝ) / 1000 := by
  have hl : 2 ^ 14526 ≤ Nat.lcmUpto 10067 := by decide +kernel
  have hu : Nat.lcmUpto 10067 ≤ 2 ^ (14526 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 10069. -/
private theorem psi_10069_bounds :
    (10077666 : ℝ) / 1000 ≤ Chebyshev.psi 10069 ∧ Chebyshev.psi 10069 ≤ (10078361 : ℝ) / 1000 := by
  have hl : 2 ^ 14539 ≤ Nat.lcmUpto 10069 := by decide +kernel
  have hu : Nat.lcmUpto 10069 ≤ 2 ^ (14539 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 10253. -/
private theorem psi_10253_bounds :
    (10275906 : ℝ) / 1000 ≤ Chebyshev.psi 10253 ∧ Chebyshev.psi 10253 ≤ (10276601 : ℝ) / 1000 := by
  have hl : 2 ^ 14825 ≤ Nat.lcmUpto 10253 := by decide +kernel
  have hu : Nat.lcmUpto 10253 ≤ 2 ^ (14825 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 10259. -/
private theorem psi_10259_bounds :
    (10284917 : ℝ) / 1000 ≤ Chebyshev.psi 10259 ∧ Chebyshev.psi 10259 ≤ (10285612 : ℝ) / 1000 := by
  have hl : 2 ^ 14838 ≤ Nat.lcmUpto 10259 := by decide +kernel
  have hu : Nat.lcmUpto 10259 ≤ 2 ^ (14838 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 10453. -/
private theorem psi_10453_bounds :
    (10469988 : ℝ) / 1000 ≤ Chebyshev.psi 10453 ∧ Chebyshev.psi 10453 ≤ (10470682 : ℝ) / 1000 := by
  have hl : 2 ^ 15105 ≤ Nat.lcmUpto 10453 := by decide +kernel
  have hu : Nat.lcmUpto 10453 ≤ 2 ^ (15105 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 10457. -/
private theorem psi_10457_bounds :
    (10478999 : ℝ) / 1000 ≤ Chebyshev.psi 10457 ∧ Chebyshev.psi 10457 ≤ (10479693 : ℝ) / 1000 := by
  have hl : 2 ^ 15118 ≤ Nat.lcmUpto 10457 := by decide +kernel
  have hu : Nat.lcmUpto 10457 ≤ 2 ^ (15118 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 10651. -/
private theorem psi_10651_bounds :
    (10668921 : ℝ) / 1000 ≤ Chebyshev.psi 10651 ∧ Chebyshev.psi 10651 ≤ (10669615 : ℝ) / 1000 := by
  have hl : 2 ^ 15392 ≤ Nat.lcmUpto 10651 := by decide +kernel
  have hu : Nat.lcmUpto 10651 ≤ 2 ^ (15392 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 10657. -/
private theorem psi_10657_bounds :
    (10678625 : ℝ) / 1000 ≤ Chebyshev.psi 10657 ∧ Chebyshev.psi 10657 ≤ (10679319 : ℝ) / 1000 := by
  have hl : 2 ^ 15406 ≤ Nat.lcmUpto 10657 := by decide +kernel
  have hu : Nat.lcmUpto 10657 ≤ 2 ^ (15406 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 10859. -/
private theorem psi_10859_bounds :
    (10864388 : ℝ) / 1000 ≤ Chebyshev.psi 10859 ∧ Chebyshev.psi 10859 ≤ (10865083 : ℝ) / 1000 := by
  have hl : 2 ^ 15674 ≤ Nat.lcmUpto 10859 := by decide +kernel
  have hu : Nat.lcmUpto 10859 ≤ 2 ^ (15674 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 10861. -/
private theorem psi_10861_bounds :
    (10873399 : ℝ) / 1000 ≤ Chebyshev.psi 10861 ∧ Chebyshev.psi 10861 ≤ (10874093 : ℝ) / 1000 := by
  have hl : 2 ^ 15687 ≤ Nat.lcmUpto 10861 := by decide +kernel
  have hu : Nat.lcmUpto 10861 ≤ 2 ^ (15687 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 11071. -/
private theorem psi_11071_bounds :
    (11068867 : ℝ) / 1000 ≤ Chebyshev.psi 11071 ∧ Chebyshev.psi 11071 ≤ (11069561 : ℝ) / 1000 := by
  have hl : 2 ^ 15969 ≤ Nat.lcmUpto 11071 := by decide +kernel
  have hu : Nat.lcmUpto 11071 ≤ 2 ^ (15969 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- A rational certificate bounds the envelope from 8305 onward. -/
private theorem batch_envelope {t : ℝ} (ht : 8305 ≤ t) :
    (215 : ℝ) ≤
      Real.sqrt t * (Real.log t * (Real.log t - Real.log (Real.log t)) / (8 * Real.pi)) := by
  have h :=
    lee_nosal_envelope_of_log_checks (N := 8305) (lo := 902 / 100) (hi := 903 / 100) (vlo :=
      219 / 100) (vhi := 221 / 100) (c := 215) (j := 14) (k := 4) (n := 32) (m := 32)
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by decide +kernel) (by decide +kernel) (by norm_num only)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact
    h.trans
      (lee_nosal_envelope_mono (x := 8305) (y := t)
        (Real.exp_one_lt_three.le.trans (by norm_num only)) ht)

/-- Every batch cell has a checked psi lower bound. -/
private theorem batch_lower : ∀ r ∈ batchCells, (r.lo : ℝ) / 1000 ≤ Chebyshev.psi r.a := by
  intro r hr
  simp only [batchCells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change (8303210 : ℝ) / 1000 ≤ Chebyshev.psi (↑(8305 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 8297) (b := 8305) (by decide) (by decide +kernel)]
    exact psi_8297_bounds.1
  · change (8474417 : ℝ) / 1000 ≤ Chebyshev.psi (↑(8518 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 8513) (b := 8518) (by decide) (by decide +kernel)]
    exact psi_8513_bounds.1
  · change (8665032 : ℝ) / 1000 ≤ Chebyshev.psi (↑(8689 : ℕ) : ℝ)
    exact psi_8689_bounds.1
  · change (8882681 : ℝ) / 1000 ≤ Chebyshev.psi (↑(8880 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 8867) (b := 8880) (by decide) (by decide +kernel)]
    exact psi_8867_bounds.1
  · change (9083000 : ℝ) / 1000 ≤ Chebyshev.psi (↑(9097 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 9091) (b := 9097) (by decide) (by decide +kernel)]
    exact psi_9091_bounds.1
  · change (9293024 : ℝ) / 1000 ≤ Chebyshev.psi (↑(9298 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 9293) (b := 9298) (by decide) (by decide +kernel)]
    exact psi_9293_bounds.1
  · change (9516910 : ℝ) / 1000 ≤ Chebyshev.psi (↑(9479 : ℕ) : ℝ)
    exact psi_9479_bounds.1
  · change (9700594 : ℝ) / 1000 ≤ Chebyshev.psi (↑(9679 : ℕ) : ℝ)
    exact psi_9679_bounds.1
  · change (9902300 : ℝ) / 1000 ≤ Chebyshev.psi (↑(9859 : ℕ) : ℝ)
    exact psi_9859_bounds.1
  · change (10077666 : ℝ) / 1000 ≤ Chebyshev.psi (↑(10069 : ℕ) : ℝ)
    exact psi_10069_bounds.1
  · change (10284917 : ℝ) / 1000 ≤ Chebyshev.psi (↑(10259 : ℕ) : ℝ)
    exact psi_10259_bounds.1
  · change (10478999 : ℝ) / 1000 ≤ Chebyshev.psi (↑(10457 : ℕ) : ℝ)
    exact psi_10457_bounds.1
  · change (10678625 : ℝ) / 1000 ≤ Chebyshev.psi (↑(10657 : ℕ) : ℝ)
    exact psi_10657_bounds.1
  · change (10873399 : ℝ) / 1000 ≤ Chebyshev.psi (↑(10861 : ℕ) : ℝ)
    exact psi_10861_bounds.1

/-- Every batch cell has a checked psi upper bound. -/
private theorem batch_upper :
    ∀ r ∈ batchCells, Chebyshev.psi (r.b - 1 : ℕ) ≤ (r.hi : ℝ) / 1000 := by
  intro r hr
  simp only [batchCells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change Chebyshev.psi (↑(8517 : ℕ) : ℝ) ≤ (8475111 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 8513) (b := 8517) (by decide) (by decide +kernel)]
    exact psi_8513_bounds.2
  · change Chebyshev.psi (↑(8688 : ℕ) : ℝ) ≤ (8656716 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 8681) (b := 8688) (by decide) (by decide +kernel)]
    exact psi_8681_bounds.2
  · change Chebyshev.psi (↑(8879 : ℕ) : ℝ) ≤ (8883375 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 8867) (b := 8879) (by decide) (by decide +kernel)]
    exact psi_8867_bounds.2
  · change Chebyshev.psi (↑(9096 : ℕ) : ℝ) ≤ (9083694 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 9091) (b := 9096) (by decide) (by decide +kernel)]
    exact psi_9091_bounds.2
  · change Chebyshev.psi (↑(9297 : ℕ) : ℝ) ≤ (9293718 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 9293) (b := 9297) (by decide) (by decide +kernel)]
    exact psi_9293_bounds.2
  · change Chebyshev.psi (↑(9478 : ℕ) : ℝ) ≤ (9508594 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 9473) (b := 9478) (by decide) (by decide +kernel)]
    exact psi_9473_bounds.2
  · change Chebyshev.psi (↑(9678 : ℕ) : ℝ) ≤ (9692278 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 9677) (b := 9678) (by decide) (by decide +kernel)]
    exact psi_9677_bounds.2
  · change Chebyshev.psi (↑(9858 : ℕ) : ℝ) ≤ (9893983 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 9857) (b := 9858) (by decide) (by decide +kernel)]
    exact psi_9857_bounds.2
  · change Chebyshev.psi (↑(10068 : ℕ) : ℝ) ≤ (10069350 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 10067) (b := 10068) (by decide)
        (by decide +kernel)]
    exact psi_10067_bounds.2
  · change Chebyshev.psi (↑(10258 : ℕ) : ℝ) ≤ (10276601 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 10253) (b := 10258) (by decide)
        (by decide +kernel)]
    exact psi_10253_bounds.2
  · change Chebyshev.psi (↑(10456 : ℕ) : ℝ) ≤ (10470682 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 10453) (b := 10456) (by decide)
        (by decide +kernel)]
    exact psi_10453_bounds.2
  · change Chebyshev.psi (↑(10656 : ℕ) : ℝ) ≤ (10669615 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 10651) (b := 10656) (by decide)
        (by decide +kernel)]
    exact psi_10651_bounds.2
  · change Chebyshev.psi (↑(10860 : ℕ) : ℝ) ≤ (10865083 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 10859) (b := 10860) (by decide)
        (by decide +kernel)]
    exact psi_10859_bounds.2
  · change Chebyshev.psi (↑(11082 : ℕ) : ℝ) ≤ (11069561 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 11071) (b := 11082) (by decide)
        (by decide +kernel)]
    exact psi_11071_bounds.2

/-- The envelope bound applies at every cell a endpoint. -/
private theorem batch_a :
    ∀ r ∈ batchCells,
      (r.ca : ℝ) / 1000 ≤
        Real.sqrt r.a *
          (Real.log r.a * (Real.log r.a - Real.log (Real.log r.a)) / (8 * Real.pi)) := by
  intro r hr
  simp only [batchCells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change
      (215000 : ℝ) / 1000 ≤
        Real.sqrt 8305 *
          (Real.log 8305 * (Real.log 8305 - Real.log (Real.log 8305)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (215000 : ℝ) / 1000 ≤
        Real.sqrt 8518 *
          (Real.log 8518 * (Real.log 8518 - Real.log (Real.log 8518)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (215000 : ℝ) / 1000 ≤
        Real.sqrt 8689 *
          (Real.log 8689 * (Real.log 8689 - Real.log (Real.log 8689)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (215000 : ℝ) / 1000 ≤
        Real.sqrt 8880 *
          (Real.log 8880 * (Real.log 8880 - Real.log (Real.log 8880)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (215000 : ℝ) / 1000 ≤
        Real.sqrt 9097 *
          (Real.log 9097 * (Real.log 9097 - Real.log (Real.log 9097)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (215000 : ℝ) / 1000 ≤
        Real.sqrt 9298 *
          (Real.log 9298 * (Real.log 9298 - Real.log (Real.log 9298)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (215000 : ℝ) / 1000 ≤
        Real.sqrt 9479 *
          (Real.log 9479 * (Real.log 9479 - Real.log (Real.log 9479)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (215000 : ℝ) / 1000 ≤
        Real.sqrt 9679 *
          (Real.log 9679 * (Real.log 9679 - Real.log (Real.log 9679)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (215000 : ℝ) / 1000 ≤
        Real.sqrt 9859 *
          (Real.log 9859 * (Real.log 9859 - Real.log (Real.log 9859)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (215000 : ℝ) / 1000 ≤
        Real.sqrt 10069 *
          (Real.log 10069 * (Real.log 10069 - Real.log (Real.log 10069)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (215000 : ℝ) / 1000 ≤
        Real.sqrt 10259 *
          (Real.log 10259 * (Real.log 10259 - Real.log (Real.log 10259)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (215000 : ℝ) / 1000 ≤
        Real.sqrt 10457 *
          (Real.log 10457 * (Real.log 10457 - Real.log (Real.log 10457)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (215000 : ℝ) / 1000 ≤
        Real.sqrt 10657 *
          (Real.log 10657 * (Real.log 10657 - Real.log (Real.log 10657)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (215000 : ℝ) / 1000 ≤
        Real.sqrt 10861 *
          (Real.log 10861 * (Real.log 10861 - Real.log (Real.log 10861)) / (8 * Real.pi))
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
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change
      (215000 : ℝ) / 1000 ≤
        Real.sqrt 8518 *
          (Real.log 8518 * (Real.log 8518 - Real.log (Real.log 8518)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (215000 : ℝ) / 1000 ≤
        Real.sqrt 8689 *
          (Real.log 8689 * (Real.log 8689 - Real.log (Real.log 8689)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (215000 : ℝ) / 1000 ≤
        Real.sqrt 8880 *
          (Real.log 8880 * (Real.log 8880 - Real.log (Real.log 8880)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (215000 : ℝ) / 1000 ≤
        Real.sqrt 9097 *
          (Real.log 9097 * (Real.log 9097 - Real.log (Real.log 9097)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (215000 : ℝ) / 1000 ≤
        Real.sqrt 9298 *
          (Real.log 9298 * (Real.log 9298 - Real.log (Real.log 9298)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (215000 : ℝ) / 1000 ≤
        Real.sqrt 9479 *
          (Real.log 9479 * (Real.log 9479 - Real.log (Real.log 9479)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (215000 : ℝ) / 1000 ≤
        Real.sqrt 9679 *
          (Real.log 9679 * (Real.log 9679 - Real.log (Real.log 9679)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (215000 : ℝ) / 1000 ≤
        Real.sqrt 9859 *
          (Real.log 9859 * (Real.log 9859 - Real.log (Real.log 9859)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (215000 : ℝ) / 1000 ≤
        Real.sqrt 10069 *
          (Real.log 10069 * (Real.log 10069 - Real.log (Real.log 10069)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (215000 : ℝ) / 1000 ≤
        Real.sqrt 10259 *
          (Real.log 10259 * (Real.log 10259 - Real.log (Real.log 10259)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (215000 : ℝ) / 1000 ≤
        Real.sqrt 10457 *
          (Real.log 10457 * (Real.log 10457 - Real.log (Real.log 10457)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (215000 : ℝ) / 1000 ≤
        Real.sqrt 10657 *
          (Real.log 10657 * (Real.log 10657 - Real.log (Real.log 10657)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (215000 : ℝ) / 1000 ≤
        Real.sqrt 10861 *
          (Real.log 10861 * (Real.log 10861 - Real.log (Real.log 10861)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (215000 : ℝ) / 1000 ≤
        Real.sqrt 11083 *
          (Real.log 11083 * (Real.log 11083 - Real.log (Real.log 11083)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)

/-- The checked batch proves the Lee–Nosal psi estimate on `[8305, 11083)`. -/
theorem psi_lee_nosal_8305_11083 {x : ℝ} (ha : 8305 ≤ x) (hb : x < 11083) :
    |Chebyshev.psi x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  exact
    lee_nosal_chain_sound Chebyshev.psi_mono Chebyshev.psi_eq_psi_coe_floor (by decide +kernel)
      batch_lower batch_upper batch_a batch_b ha hb

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
