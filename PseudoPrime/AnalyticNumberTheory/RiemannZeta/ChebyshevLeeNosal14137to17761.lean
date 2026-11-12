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
  [⟨14137, 14435, 14115942, 14393895, 320000, 320000⟩,
    ⟨14435, 14713, 14393201, 14664915, 320000, 320000⟩,
    ⟨14713, 14993, 14673925, 14991388, 320000, 320000⟩,
    ⟨14993, 15307, 14990694, 15308849, 320000, 320000⟩,
    ⟨15307, 15607, 15317859, 15617993, 320000, 320000⟩,
    ⟨15607, 15887, 15627003, 15918819, 320000, 320000⟩,
    ⟨15887, 16183, 15927829, 16204395, 320000, 320000⟩,
    ⟨16183, 16481, 16213405, 16496210, 320000, 320000⟩,
    ⟨16481, 16823, 16505220, 16799809, 320000, 320000⟩,
    ⟨16823, 17128, 16808819, 17130440, 320000, 320000⟩,
    ⟨17128, 17449, 17129746, 17447901, 320000, 320000⟩,
    ⟨17449, 17761, 17456911, 17760511, 320000, 320000⟩]

/-- The kernel-checked prefix bounds for 14107. -/
private theorem psi_14107_bounds :
    (14115942 : ℝ) / 1000 ≤ Chebyshev.psi 14107 ∧ Chebyshev.psi 14107 ≤ (14116636 : ℝ) / 1000 := by
  have hl : 2 ^ 20365 ≤ Nat.lcmUpto 14107 := by decide +kernel
  have hu : Nat.lcmUpto 14107 ≤ 2 ^ (20365 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 14431. -/
private theorem psi_14431_bounds :
    (14393201 : ℝ) / 1000 ≤ Chebyshev.psi 14431 ∧ Chebyshev.psi 14431 ≤ (14393895 : ℝ) / 1000 := by
  have hl : 2 ^ 20765 ≤ Nat.lcmUpto 14431 := by decide +kernel
  have hu : Nat.lcmUpto 14431 ≤ 2 ^ (20765 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 14699. -/
private theorem psi_14699_bounds :
    (14664221 : ℝ) / 1000 ≤ Chebyshev.psi 14699 ∧ Chebyshev.psi 14699 ≤ (14664915 : ℝ) / 1000 := by
  have hl : 2 ^ 21156 ≤ Nat.lcmUpto 14699 := by decide +kernel
  have hu : Nat.lcmUpto 14699 ≤ 2 ^ (21156 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 14713. -/
private theorem psi_14713_bounds :
    (14673925 : ℝ) / 1000 ≤ Chebyshev.psi 14713 ∧ Chebyshev.psi 14713 ≤ (14674619 : ℝ) / 1000 := by
  have hl : 2 ^ 21170 ≤ Nat.lcmUpto 14713 := by decide +kernel
  have hu : Nat.lcmUpto 14713 ≤ 2 ^ (21170 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 14983. -/
private theorem psi_14983_bounds :
    (14990694 : ℝ) / 1000 ≤ Chebyshev.psi 14983 ∧ Chebyshev.psi 14983 ≤ (14991388 : ℝ) / 1000 := by
  have hl : 2 ^ 21627 ≤ Nat.lcmUpto 14983 := by decide +kernel
  have hu : Nat.lcmUpto 14983 ≤ 2 ^ (21627 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 15299. -/
private theorem psi_15299_bounds :
    (15308155 : ℝ) / 1000 ≤ Chebyshev.psi 15299 ∧ Chebyshev.psi 15299 ≤ (15308849 : ℝ) / 1000 := by
  have hl : 2 ^ 22085 ≤ Nat.lcmUpto 15299 := by decide +kernel
  have hu : Nat.lcmUpto 15299 ≤ 2 ^ (22085 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 15307. -/
private theorem psi_15307_bounds :
    (15317859 : ℝ) / 1000 ≤ Chebyshev.psi 15307 ∧ Chebyshev.psi 15307 ≤ (15318553 : ℝ) / 1000 := by
  have hl : 2 ^ 22099 ≤ Nat.lcmUpto 15307 := by decide +kernel
  have hu : Nat.lcmUpto 15307 ≤ 2 ^ (22099 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 15601. -/
private theorem psi_15601_bounds :
    (15617299 : ℝ) / 1000 ≤ Chebyshev.psi 15601 ∧ Chebyshev.psi 15601 ≤ (15617993 : ℝ) / 1000 := by
  have hl : 2 ^ 22531 ≤ Nat.lcmUpto 15601 := by decide +kernel
  have hu : Nat.lcmUpto 15601 ≤ 2 ^ (22531 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 15607. -/
private theorem psi_15607_bounds :
    (15627003 : ℝ) / 1000 ≤ Chebyshev.psi 15607 ∧ Chebyshev.psi 15607 ≤ (15627697 : ℝ) / 1000 := by
  have hl : 2 ^ 22545 ≤ Nat.lcmUpto 15607 := by decide +kernel
  have hu : Nat.lcmUpto 15607 ≤ 2 ^ (22545 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 15881. -/
private theorem psi_15881_bounds :
    (15918124 : ℝ) / 1000 ≤ Chebyshev.psi 15881 ∧ Chebyshev.psi 15881 ≤ (15918819 : ℝ) / 1000 := by
  have hl : 2 ^ 22965 ≤ Nat.lcmUpto 15881 := by decide +kernel
  have hu : Nat.lcmUpto 15881 ≤ 2 ^ (22965 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 15887. -/
private theorem psi_15887_bounds :
    (15927829 : ℝ) / 1000 ≤ Chebyshev.psi 15887 ∧ Chebyshev.psi 15887 ≤ (15928523 : ℝ) / 1000 := by
  have hl : 2 ^ 22979 ≤ Nat.lcmUpto 15887 := by decide +kernel
  have hu : Nat.lcmUpto 15887 ≤ 2 ^ (22979 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 16141. -/
private theorem psi_16141_bounds :
    (16203701 : ℝ) / 1000 ≤ Chebyshev.psi 16141 ∧ Chebyshev.psi 16141 ≤ (16204395 : ℝ) / 1000 := by
  have hl : 2 ^ 23377 ≤ Nat.lcmUpto 16141 := by decide +kernel
  have hu : Nat.lcmUpto 16141 ≤ 2 ^ (23377 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 16183. -/
private theorem psi_16183_bounds :
    (16213405 : ℝ) / 1000 ≤ Chebyshev.psi 16183 ∧ Chebyshev.psi 16183 ≤ (16214099 : ℝ) / 1000 := by
  have hl : 2 ^ 23391 ≤ Nat.lcmUpto 16183 := by decide +kernel
  have hu : Nat.lcmUpto 16183 ≤ 2 ^ (23391 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 16477. -/
private theorem psi_16477_bounds :
    (16495516 : ℝ) / 1000 ≤ Chebyshev.psi 16477 ∧ Chebyshev.psi 16477 ≤ (16496210 : ℝ) / 1000 := by
  have hl : 2 ^ 23798 ≤ Nat.lcmUpto 16477 := by decide +kernel
  have hu : Nat.lcmUpto 16477 ≤ 2 ^ (23798 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 16481. -/
private theorem psi_16481_bounds :
    (16505220 : ℝ) / 1000 ≤ Chebyshev.psi 16481 ∧ Chebyshev.psi 16481 ≤ (16505914 : ℝ) / 1000 := by
  have hl : 2 ^ 23812 ≤ Nat.lcmUpto 16481 := by decide +kernel
  have hu : Nat.lcmUpto 16481 ≤ 2 ^ (23812 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 16811. -/
private theorem psi_16811_bounds :
    (16799115 : ℝ) / 1000 ≤ Chebyshev.psi 16811 ∧ Chebyshev.psi 16811 ≤ (16799809 : ℝ) / 1000 := by
  have hl : 2 ^ 24236 ≤ Nat.lcmUpto 16811 := by decide +kernel
  have hu : Nat.lcmUpto 16811 ≤ 2 ^ (24236 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 16823. -/
private theorem psi_16823_bounds :
    (16808819 : ℝ) / 1000 ≤ Chebyshev.psi 16823 ∧ Chebyshev.psi 16823 ≤ (16809513 : ℝ) / 1000 := by
  have hl : 2 ^ 24250 ≤ Nat.lcmUpto 16823 := by decide +kernel
  have hu : Nat.lcmUpto 16823 ≤ 2 ^ (24250 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 17123. -/
private theorem psi_17123_bounds :
    (17129746 : ℝ) / 1000 ≤ Chebyshev.psi 17123 ∧ Chebyshev.psi 17123 ≤ (17130440 : ℝ) / 1000 := by
  have hl : 2 ^ 24713 ≤ Nat.lcmUpto 17123 := by decide +kernel
  have hu : Nat.lcmUpto 17123 ≤ 2 ^ (24713 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 17443. -/
private theorem psi_17443_bounds :
    (17447207 : ℝ) / 1000 ≤ Chebyshev.psi 17443 ∧ Chebyshev.psi 17443 ≤ (17447901 : ℝ) / 1000 := by
  have hl : 2 ^ 25171 ≤ Nat.lcmUpto 17443 := by decide +kernel
  have hu : Nat.lcmUpto 17443 ≤ 2 ^ (25171 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 17449. -/
private theorem psi_17449_bounds :
    (17456911 : ℝ) / 1000 ≤ Chebyshev.psi 17449 ∧ Chebyshev.psi 17449 ≤ (17457605 : ℝ) / 1000 := by
  have hl : 2 ^ 25185 ≤ Nat.lcmUpto 17449 := by decide +kernel
  have hu : Nat.lcmUpto 17449 ≤ 2 ^ (25185 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 17749. -/
private theorem psi_17749_bounds :
    (17759817 : ℝ) / 1000 ≤ Chebyshev.psi 17749 ∧ Chebyshev.psi 17749 ≤ (17760511 : ℝ) / 1000 := by
  have hl : 2 ^ 25622 ≤ Nat.lcmUpto 17749 := by decide +kernel
  have hu : Nat.lcmUpto 17749 ≤ 2 ^ (25622 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- A rational certificate bounds the envelope from 14137 onward. -/
private theorem batch_envelope {t : ℝ} (ht : 14137 ≤ t) :
    (320 : ℝ) ≤
      Real.sqrt t * (Real.log t * (Real.log t - Real.log (Real.log t)) / (8 * Real.pi)) := by
  have h :=
    lee_nosal_envelope_of_log_checks (N := 14137) (lo := 955 / 100) (hi := 956 / 100) (vlo :=
      225 / 100) (vhi := 226 / 100) (c := 320) (j := 14) (k := 4) (n := 32) (m := 32)
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by decide +kernel) (by decide +kernel) (by norm_num only)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact
    h.trans
      (lee_nosal_envelope_mono (x := 14137) (y := t)
        (Real.exp_one_lt_three.le.trans (by norm_num only)) ht)

/-- Every batch cell has a checked psi lower bound. -/
private theorem batch_lower : ∀ r ∈ batchCells, (r.lo : ℝ) / 1000 ≤ Chebyshev.psi r.a := by
  intro r hr
  simp only [batchCells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change (14115942 : ℝ) / 1000 ≤ Chebyshev.psi (↑(14137 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 14107) (b := 14137) (by decide)
        (by decide +kernel)]
    exact psi_14107_bounds.1
  · change (14393201 : ℝ) / 1000 ≤ Chebyshev.psi (↑(14435 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 14431) (b := 14435) (by decide)
        (by decide +kernel)]
    exact psi_14431_bounds.1
  · change (14673925 : ℝ) / 1000 ≤ Chebyshev.psi (↑(14713 : ℕ) : ℝ)
    exact psi_14713_bounds.1
  · change (14990694 : ℝ) / 1000 ≤ Chebyshev.psi (↑(14993 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 14983) (b := 14993) (by decide)
        (by decide +kernel)]
    exact psi_14983_bounds.1
  · change (15317859 : ℝ) / 1000 ≤ Chebyshev.psi (↑(15307 : ℕ) : ℝ)
    exact psi_15307_bounds.1
  · change (15627003 : ℝ) / 1000 ≤ Chebyshev.psi (↑(15607 : ℕ) : ℝ)
    exact psi_15607_bounds.1
  · change (15927829 : ℝ) / 1000 ≤ Chebyshev.psi (↑(15887 : ℕ) : ℝ)
    exact psi_15887_bounds.1
  · change (16213405 : ℝ) / 1000 ≤ Chebyshev.psi (↑(16183 : ℕ) : ℝ)
    exact psi_16183_bounds.1
  · change (16505220 : ℝ) / 1000 ≤ Chebyshev.psi (↑(16481 : ℕ) : ℝ)
    exact psi_16481_bounds.1
  · change (16808819 : ℝ) / 1000 ≤ Chebyshev.psi (↑(16823 : ℕ) : ℝ)
    exact psi_16823_bounds.1
  · change (17129746 : ℝ) / 1000 ≤ Chebyshev.psi (↑(17128 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 17123) (b := 17128) (by decide)
        (by decide +kernel)]
    exact psi_17123_bounds.1
  · change (17456911 : ℝ) / 1000 ≤ Chebyshev.psi (↑(17449 : ℕ) : ℝ)
    exact psi_17449_bounds.1

/-- Every batch cell has a checked psi upper bound. -/
private theorem batch_upper :
    ∀ r ∈ batchCells, Chebyshev.psi (r.b - 1 : ℕ) ≤ (r.hi : ℝ) / 1000 := by
  intro r hr
  simp only [batchCells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change Chebyshev.psi (↑(14434 : ℕ) : ℝ) ≤ (14393895 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 14431) (b := 14434) (by decide)
        (by decide +kernel)]
    exact psi_14431_bounds.2
  · change Chebyshev.psi (↑(14712 : ℕ) : ℝ) ≤ (14664915 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 14699) (b := 14712) (by decide)
        (by decide +kernel)]
    exact psi_14699_bounds.2
  · change Chebyshev.psi (↑(14992 : ℕ) : ℝ) ≤ (14991388 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 14983) (b := 14992) (by decide)
        (by decide +kernel)]
    exact psi_14983_bounds.2
  · change Chebyshev.psi (↑(15306 : ℕ) : ℝ) ≤ (15308849 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 15299) (b := 15306) (by decide)
        (by decide +kernel)]
    exact psi_15299_bounds.2
  · change Chebyshev.psi (↑(15606 : ℕ) : ℝ) ≤ (15617993 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 15601) (b := 15606) (by decide)
        (by decide +kernel)]
    exact psi_15601_bounds.2
  · change Chebyshev.psi (↑(15886 : ℕ) : ℝ) ≤ (15918819 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 15881) (b := 15886) (by decide)
        (by decide +kernel)]
    exact psi_15881_bounds.2
  · change Chebyshev.psi (↑(16182 : ℕ) : ℝ) ≤ (16204395 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 16141) (b := 16182) (by decide)
        (by decide +kernel)]
    exact psi_16141_bounds.2
  · change Chebyshev.psi (↑(16480 : ℕ) : ℝ) ≤ (16496210 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 16477) (b := 16480) (by decide)
        (by decide +kernel)]
    exact psi_16477_bounds.2
  · change Chebyshev.psi (↑(16822 : ℕ) : ℝ) ≤ (16799809 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 16811) (b := 16822) (by decide)
        (by decide +kernel)]
    exact psi_16811_bounds.2
  · change Chebyshev.psi (↑(17127 : ℕ) : ℝ) ≤ (17130440 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 17123) (b := 17127) (by decide)
        (by decide +kernel)]
    exact psi_17123_bounds.2
  · change Chebyshev.psi (↑(17448 : ℕ) : ℝ) ≤ (17447901 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 17443) (b := 17448) (by decide)
        (by decide +kernel)]
    exact psi_17443_bounds.2
  · change Chebyshev.psi (↑(17760 : ℕ) : ℝ) ≤ (17760511 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 17749) (b := 17760) (by decide)
        (by decide +kernel)]
    exact psi_17749_bounds.2

/-- The envelope bound applies at every cell a endpoint. -/
private theorem batch_a :
    ∀ r ∈ batchCells,
      (r.ca : ℝ) / 1000 ≤
        Real.sqrt r.a *
          (Real.log r.a * (Real.log r.a - Real.log (Real.log r.a)) / (8 * Real.pi)) := by
  intro r hr
  simp only [batchCells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change
      (320000 : ℝ) / 1000 ≤
        Real.sqrt 14137 *
          (Real.log 14137 * (Real.log 14137 - Real.log (Real.log 14137)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (320000 : ℝ) / 1000 ≤
        Real.sqrt 14435 *
          (Real.log 14435 * (Real.log 14435 - Real.log (Real.log 14435)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (320000 : ℝ) / 1000 ≤
        Real.sqrt 14713 *
          (Real.log 14713 * (Real.log 14713 - Real.log (Real.log 14713)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (320000 : ℝ) / 1000 ≤
        Real.sqrt 14993 *
          (Real.log 14993 * (Real.log 14993 - Real.log (Real.log 14993)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (320000 : ℝ) / 1000 ≤
        Real.sqrt 15307 *
          (Real.log 15307 * (Real.log 15307 - Real.log (Real.log 15307)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (320000 : ℝ) / 1000 ≤
        Real.sqrt 15607 *
          (Real.log 15607 * (Real.log 15607 - Real.log (Real.log 15607)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (320000 : ℝ) / 1000 ≤
        Real.sqrt 15887 *
          (Real.log 15887 * (Real.log 15887 - Real.log (Real.log 15887)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (320000 : ℝ) / 1000 ≤
        Real.sqrt 16183 *
          (Real.log 16183 * (Real.log 16183 - Real.log (Real.log 16183)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (320000 : ℝ) / 1000 ≤
        Real.sqrt 16481 *
          (Real.log 16481 * (Real.log 16481 - Real.log (Real.log 16481)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (320000 : ℝ) / 1000 ≤
        Real.sqrt 16823 *
          (Real.log 16823 * (Real.log 16823 - Real.log (Real.log 16823)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (320000 : ℝ) / 1000 ≤
        Real.sqrt 17128 *
          (Real.log 17128 * (Real.log 17128 - Real.log (Real.log 17128)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (320000 : ℝ) / 1000 ≤
        Real.sqrt 17449 *
          (Real.log 17449 * (Real.log 17449 - Real.log (Real.log 17449)) / (8 * Real.pi))
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
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change
      (320000 : ℝ) / 1000 ≤
        Real.sqrt 14435 *
          (Real.log 14435 * (Real.log 14435 - Real.log (Real.log 14435)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (320000 : ℝ) / 1000 ≤
        Real.sqrt 14713 *
          (Real.log 14713 * (Real.log 14713 - Real.log (Real.log 14713)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (320000 : ℝ) / 1000 ≤
        Real.sqrt 14993 *
          (Real.log 14993 * (Real.log 14993 - Real.log (Real.log 14993)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (320000 : ℝ) / 1000 ≤
        Real.sqrt 15307 *
          (Real.log 15307 * (Real.log 15307 - Real.log (Real.log 15307)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (320000 : ℝ) / 1000 ≤
        Real.sqrt 15607 *
          (Real.log 15607 * (Real.log 15607 - Real.log (Real.log 15607)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (320000 : ℝ) / 1000 ≤
        Real.sqrt 15887 *
          (Real.log 15887 * (Real.log 15887 - Real.log (Real.log 15887)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (320000 : ℝ) / 1000 ≤
        Real.sqrt 16183 *
          (Real.log 16183 * (Real.log 16183 - Real.log (Real.log 16183)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (320000 : ℝ) / 1000 ≤
        Real.sqrt 16481 *
          (Real.log 16481 * (Real.log 16481 - Real.log (Real.log 16481)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (320000 : ℝ) / 1000 ≤
        Real.sqrt 16823 *
          (Real.log 16823 * (Real.log 16823 - Real.log (Real.log 16823)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (320000 : ℝ) / 1000 ≤
        Real.sqrt 17128 *
          (Real.log 17128 * (Real.log 17128 - Real.log (Real.log 17128)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (320000 : ℝ) / 1000 ≤
        Real.sqrt 17449 *
          (Real.log 17449 * (Real.log 17449 - Real.log (Real.log 17449)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (320000 : ℝ) / 1000 ≤
        Real.sqrt 17761 *
          (Real.log 17761 * (Real.log 17761 - Real.log (Real.log 17761)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)

/-- The checked batch proves the Lee–Nosal psi estimate on `[14137, 17761)`. -/
theorem psi_lee_nosal_14137_17761 {x : ℝ} (ha : 14137 ≤ x) (hb : x < 17761) :
    |Chebyshev.psi x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  exact
    lee_nosal_chain_sound Chebyshev.psi_mono Chebyshev.psi_eq_psi_coe_floor (by decide +kernel)
      batch_lower batch_upper batch_a batch_b ha hb

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
