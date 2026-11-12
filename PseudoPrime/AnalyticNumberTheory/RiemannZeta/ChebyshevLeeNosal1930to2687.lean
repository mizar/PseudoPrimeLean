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
  [⟨1930, 1989, 1917938, 1972004, 72000, 72000⟩, ⟨1989, 2043, 1971310, 2040626, 72000, 72000⟩,
    ⟨2043, 2111, 2039932, 2102316, 72000, 72000⟩, ⟨2111, 2181, 2109246, 2179255, 72000, 72000⟩,
    ⟨2181, 2250, 2178561, 2240252, 72000, 72000⟩, ⟨2250, 2311, 2239558, 2310260, 72000, 72000⟩,
    ⟨2311, 2381, 2317191, 2379575, 72000, 72000⟩, ⟨2381, 2441, 2387198, 2451662, 72000, 72000⟩,
    ⟨2441, 2521, 2459286, 2506421, 72000, 72000⟩, ⟨2521, 2585, 2513351, 2569497, 72000, 72000⟩,
    ⟨2585, 2640, 2568803, 2616631, 72000, 72000⟩, ⟨2640, 2687, 2615937, 2671390, 72000, 72000⟩]

/-- The kernel-checked prefix bounds for 1913. -/
private theorem psi_1913_bounds :
    (1917938 : ℝ) / 1000 ≤ Chebyshev.psi 1913 ∧ Chebyshev.psi 1913 ≤ (1918632 : ℝ) / 1000 := by
  have hl : 2 ^ 2767 ≤ Nat.lcmUpto 1913 := by decide +kernel
  have hu : Nat.lcmUpto 1913 ≤ 2 ^ (2767 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 1987. -/
private theorem psi_1987_bounds :
    (1971310 : ℝ) / 1000 ≤ Chebyshev.psi 1987 ∧ Chebyshev.psi 1987 ≤ (1972004 : ℝ) / 1000 := by
  have hl : 2 ^ 2844 ≤ Nat.lcmUpto 1987 := by decide +kernel
  have hu : Nat.lcmUpto 1987 ≤ 2 ^ (2844 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 2039. -/
private theorem psi_2039_bounds :
    (2039932 : ℝ) / 1000 ≤ Chebyshev.psi 2039 ∧ Chebyshev.psi 2039 ≤ (2040626 : ℝ) / 1000 := by
  have hl : 2 ^ 2943 ≤ Nat.lcmUpto 2039 := by decide +kernel
  have hu : Nat.lcmUpto 2039 ≤ 2 ^ (2943 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 2099. -/
private theorem psi_2099_bounds :
    (2101622 : ℝ) / 1000 ≤ Chebyshev.psi 2099 ∧ Chebyshev.psi 2099 ≤ (2102316 : ℝ) / 1000 := by
  have hl : 2 ^ 3032 ≤ Nat.lcmUpto 2099 := by decide +kernel
  have hu : Nat.lcmUpto 2099 ≤ 2 ^ (3032 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 2111. -/
private theorem psi_2111_bounds :
    (2109246 : ℝ) / 1000 ≤ Chebyshev.psi 2111 ∧ Chebyshev.psi 2111 ≤ (2109941 : ℝ) / 1000 := by
  have hl : 2 ^ 3043 ≤ Nat.lcmUpto 2111 := by decide +kernel
  have hu : Nat.lcmUpto 2111 ≤ 2 ^ (3043 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 2179. -/
private theorem psi_2179_bounds :
    (2178561 : ℝ) / 1000 ≤ Chebyshev.psi 2179 ∧ Chebyshev.psi 2179 ≤ (2179255 : ℝ) / 1000 := by
  have hl : 2 ^ 3143 ≤ Nat.lcmUpto 2179 := by decide +kernel
  have hu : Nat.lcmUpto 2179 ≤ 2 ^ (3143 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 2243. -/
private theorem psi_2243_bounds :
    (2239558 : ℝ) / 1000 ≤ Chebyshev.psi 2243 ∧ Chebyshev.psi 2243 ≤ (2240252 : ℝ) / 1000 := by
  have hl : 2 ^ 3231 ≤ Nat.lcmUpto 2243 := by decide +kernel
  have hu : Nat.lcmUpto 2243 ≤ 2 ^ (3231 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 2309. -/
private theorem psi_2309_bounds :
    (2309566 : ℝ) / 1000 ≤ Chebyshev.psi 2309 ∧ Chebyshev.psi 2309 ≤ (2310260 : ℝ) / 1000 := by
  have hl : 2 ^ 3332 ≤ Nat.lcmUpto 2309 := by decide +kernel
  have hu : Nat.lcmUpto 2309 ≤ 2 ^ (3332 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 2311. -/
private theorem psi_2311_bounds :
    (2317191 : ℝ) / 1000 ≤ Chebyshev.psi 2311 ∧ Chebyshev.psi 2311 ≤ (2317885 : ℝ) / 1000 := by
  have hl : 2 ^ 3343 ≤ Nat.lcmUpto 2311 := by decide +kernel
  have hu : Nat.lcmUpto 2311 ≤ 2 ^ (3343 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 2377. -/
private theorem psi_2377_bounds :
    (2378881 : ℝ) / 1000 ≤ Chebyshev.psi 2377 ∧ Chebyshev.psi 2377 ≤ (2379575 : ℝ) / 1000 := by
  have hl : 2 ^ 3432 ≤ Nat.lcmUpto 2377 := by decide +kernel
  have hu : Nat.lcmUpto 2377 ≤ 2 ^ (3432 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 2381. -/
private theorem psi_2381_bounds :
    (2387198 : ℝ) / 1000 ≤ Chebyshev.psi 2381 ∧ Chebyshev.psi 2381 ≤ (2387893 : ℝ) / 1000 := by
  have hl : 2 ^ 3444 ≤ Nat.lcmUpto 2381 := by decide +kernel
  have hu : Nat.lcmUpto 2381 ≤ 2 ^ (3444 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 2437. -/
private theorem psi_2437_bounds :
    (2450968 : ℝ) / 1000 ≤ Chebyshev.psi 2437 ∧ Chebyshev.psi 2437 ≤ (2451662 : ℝ) / 1000 := by
  have hl : 2 ^ 3536 ≤ Nat.lcmUpto 2437 := by decide +kernel
  have hu : Nat.lcmUpto 2437 ≤ 2 ^ (3536 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 2441. -/
private theorem psi_2441_bounds :
    (2459286 : ℝ) / 1000 ≤ Chebyshev.psi 2441 ∧ Chebyshev.psi 2441 ≤ (2459980 : ℝ) / 1000 := by
  have hl : 2 ^ 3548 ≤ Nat.lcmUpto 2441 := by decide +kernel
  have hu : Nat.lcmUpto 2441 ≤ 2 ^ (3548 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 2503. -/
private theorem psi_2503_bounds :
    (2505727 : ℝ) / 1000 ≤ Chebyshev.psi 2503 ∧ Chebyshev.psi 2503 ≤ (2506421 : ℝ) / 1000 := by
  have hl : 2 ^ 3615 ≤ Nat.lcmUpto 2503 := by decide +kernel
  have hu : Nat.lcmUpto 2503 ≤ 2 ^ (3615 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 2521. -/
private theorem psi_2521_bounds :
    (2513351 : ℝ) / 1000 ≤ Chebyshev.psi 2521 ∧ Chebyshev.psi 2521 ≤ (2514045 : ℝ) / 1000 := by
  have hl : 2 ^ 3626 ≤ Nat.lcmUpto 2521 := by decide +kernel
  have hu : Nat.lcmUpto 2521 ≤ 2 ^ (3626 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 2579. -/
private theorem psi_2579_bounds :
    (2568803 : ℝ) / 1000 ≤ Chebyshev.psi 2579 ∧ Chebyshev.psi 2579 ≤ (2569497 : ℝ) / 1000 := by
  have hl : 2 ^ 3706 ≤ Nat.lcmUpto 2579 := by decide +kernel
  have hu : Nat.lcmUpto 2579 ≤ 2 ^ (3706 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 2633. -/
private theorem psi_2633_bounds :
    (2615937 : ℝ) / 1000 ≤ Chebyshev.psi 2633 ∧ Chebyshev.psi 2633 ≤ (2616631 : ℝ) / 1000 := by
  have hl : 2 ^ 3774 ≤ Nat.lcmUpto 2633 := by decide +kernel
  have hu : Nat.lcmUpto 2633 ≤ 2 ^ (3774 + 1) := by decide +kernel
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

/-- A rational certificate bounds the envelope from 1930 onward. -/
private theorem batch_envelope {t : ℝ} (ht : 1930 ≤ t) :
    (72 : ℝ) ≤
      Real.sqrt t * (Real.log t * (Real.log t - Real.log (Real.log t)) / (8 * Real.pi)) := by
  have h :=
    lee_nosal_envelope_of_log_checks (N := 1930) (lo := 756 / 100) (hi := 757 / 100) (vlo :=
      202 / 100) (vhi := 203 / 100) (c := 72) (j := 11) (k := 3) (n := 32) (m := 32)
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by decide +kernel) (by decide +kernel) (by norm_num only)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact
    h.trans
      (lee_nosal_envelope_mono (x := 1930) (y := t)
        (Real.exp_one_lt_three.le.trans (by norm_num only)) ht)

/-- Every batch cell has a checked psi lower bound. -/
private theorem batch_lower : ∀ r ∈ batchCells, (r.lo : ℝ) / 1000 ≤ Chebyshev.psi r.a := by
  intro r hr
  simp only [batchCells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change (1917938 : ℝ) / 1000 ≤ Chebyshev.psi (↑(1930 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 1913) (b := 1930) (by decide) (by decide +kernel)]
    exact psi_1913_bounds.1
  · change (1971310 : ℝ) / 1000 ≤ Chebyshev.psi (↑(1989 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 1987) (b := 1989) (by decide) (by decide +kernel)]
    exact psi_1987_bounds.1
  · change (2039932 : ℝ) / 1000 ≤ Chebyshev.psi (↑(2043 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 2039) (b := 2043) (by decide) (by decide +kernel)]
    exact psi_2039_bounds.1
  · change (2109246 : ℝ) / 1000 ≤ Chebyshev.psi (↑(2111 : ℕ) : ℝ)
    exact psi_2111_bounds.1
  · change (2178561 : ℝ) / 1000 ≤ Chebyshev.psi (↑(2181 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 2179) (b := 2181) (by decide) (by decide +kernel)]
    exact psi_2179_bounds.1
  · change (2239558 : ℝ) / 1000 ≤ Chebyshev.psi (↑(2250 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 2243) (b := 2250) (by decide) (by decide +kernel)]
    exact psi_2243_bounds.1
  · change (2317191 : ℝ) / 1000 ≤ Chebyshev.psi (↑(2311 : ℕ) : ℝ)
    exact psi_2311_bounds.1
  · change (2387198 : ℝ) / 1000 ≤ Chebyshev.psi (↑(2381 : ℕ) : ℝ)
    exact psi_2381_bounds.1
  · change (2459286 : ℝ) / 1000 ≤ Chebyshev.psi (↑(2441 : ℕ) : ℝ)
    exact psi_2441_bounds.1
  · change (2513351 : ℝ) / 1000 ≤ Chebyshev.psi (↑(2521 : ℕ) : ℝ)
    exact psi_2521_bounds.1
  · change (2568803 : ℝ) / 1000 ≤ Chebyshev.psi (↑(2585 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 2579) (b := 2585) (by decide) (by decide +kernel)]
    exact psi_2579_bounds.1
  · change (2615937 : ℝ) / 1000 ≤ Chebyshev.psi (↑(2640 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 2633) (b := 2640) (by decide) (by decide +kernel)]
    exact psi_2633_bounds.1

/-- Every batch cell has a checked psi upper bound. -/
private theorem batch_upper :
    ∀ r ∈ batchCells, Chebyshev.psi (r.b - 1 : ℕ) ≤ (r.hi : ℝ) / 1000 := by
  intro r hr
  simp only [batchCells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change Chebyshev.psi (↑(1988 : ℕ) : ℝ) ≤ (1972004 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 1987) (b := 1988) (by decide) (by decide +kernel)]
    exact psi_1987_bounds.2
  · change Chebyshev.psi (↑(2042 : ℕ) : ℝ) ≤ (2040626 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 2039) (b := 2042) (by decide) (by decide +kernel)]
    exact psi_2039_bounds.2
  · change Chebyshev.psi (↑(2110 : ℕ) : ℝ) ≤ (2102316 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 2099) (b := 2110) (by decide) (by decide +kernel)]
    exact psi_2099_bounds.2
  · change Chebyshev.psi (↑(2180 : ℕ) : ℝ) ≤ (2179255 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 2179) (b := 2180) (by decide) (by decide +kernel)]
    exact psi_2179_bounds.2
  · change Chebyshev.psi (↑(2249 : ℕ) : ℝ) ≤ (2240252 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 2243) (b := 2249) (by decide) (by decide +kernel)]
    exact psi_2243_bounds.2
  · change Chebyshev.psi (↑(2310 : ℕ) : ℝ) ≤ (2310260 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 2309) (b := 2310) (by decide) (by decide +kernel)]
    exact psi_2309_bounds.2
  · change Chebyshev.psi (↑(2380 : ℕ) : ℝ) ≤ (2379575 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 2377) (b := 2380) (by decide) (by decide +kernel)]
    exact psi_2377_bounds.2
  · change Chebyshev.psi (↑(2440 : ℕ) : ℝ) ≤ (2451662 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 2437) (b := 2440) (by decide) (by decide +kernel)]
    exact psi_2437_bounds.2
  · change Chebyshev.psi (↑(2520 : ℕ) : ℝ) ≤ (2506421 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 2503) (b := 2520) (by decide) (by decide +kernel)]
    exact psi_2503_bounds.2
  · change Chebyshev.psi (↑(2584 : ℕ) : ℝ) ≤ (2569497 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 2579) (b := 2584) (by decide) (by decide +kernel)]
    exact psi_2579_bounds.2
  · change Chebyshev.psi (↑(2639 : ℕ) : ℝ) ≤ (2616631 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 2633) (b := 2639) (by decide) (by decide +kernel)]
    exact psi_2633_bounds.2
  · change Chebyshev.psi (↑(2686 : ℕ) : ℝ) ≤ (2671390 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 2683) (b := 2686) (by decide) (by decide +kernel)]
    exact psi_2683_bounds.2

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
      (72000 : ℝ) / 1000 ≤
        Real.sqrt 1930 *
          (Real.log 1930 * (Real.log 1930 - Real.log (Real.log 1930)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (72000 : ℝ) / 1000 ≤
        Real.sqrt 1989 *
          (Real.log 1989 * (Real.log 1989 - Real.log (Real.log 1989)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (72000 : ℝ) / 1000 ≤
        Real.sqrt 2043 *
          (Real.log 2043 * (Real.log 2043 - Real.log (Real.log 2043)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (72000 : ℝ) / 1000 ≤
        Real.sqrt 2111 *
          (Real.log 2111 * (Real.log 2111 - Real.log (Real.log 2111)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (72000 : ℝ) / 1000 ≤
        Real.sqrt 2181 *
          (Real.log 2181 * (Real.log 2181 - Real.log (Real.log 2181)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (72000 : ℝ) / 1000 ≤
        Real.sqrt 2250 *
          (Real.log 2250 * (Real.log 2250 - Real.log (Real.log 2250)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (72000 : ℝ) / 1000 ≤
        Real.sqrt 2311 *
          (Real.log 2311 * (Real.log 2311 - Real.log (Real.log 2311)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (72000 : ℝ) / 1000 ≤
        Real.sqrt 2381 *
          (Real.log 2381 * (Real.log 2381 - Real.log (Real.log 2381)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (72000 : ℝ) / 1000 ≤
        Real.sqrt 2441 *
          (Real.log 2441 * (Real.log 2441 - Real.log (Real.log 2441)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (72000 : ℝ) / 1000 ≤
        Real.sqrt 2521 *
          (Real.log 2521 * (Real.log 2521 - Real.log (Real.log 2521)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (72000 : ℝ) / 1000 ≤
        Real.sqrt 2585 *
          (Real.log 2585 * (Real.log 2585 - Real.log (Real.log 2585)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (72000 : ℝ) / 1000 ≤
        Real.sqrt 2640 *
          (Real.log 2640 * (Real.log 2640 - Real.log (Real.log 2640)) / (8 * Real.pi))
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
      (72000 : ℝ) / 1000 ≤
        Real.sqrt 1989 *
          (Real.log 1989 * (Real.log 1989 - Real.log (Real.log 1989)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (72000 : ℝ) / 1000 ≤
        Real.sqrt 2043 *
          (Real.log 2043 * (Real.log 2043 - Real.log (Real.log 2043)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (72000 : ℝ) / 1000 ≤
        Real.sqrt 2111 *
          (Real.log 2111 * (Real.log 2111 - Real.log (Real.log 2111)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (72000 : ℝ) / 1000 ≤
        Real.sqrt 2181 *
          (Real.log 2181 * (Real.log 2181 - Real.log (Real.log 2181)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (72000 : ℝ) / 1000 ≤
        Real.sqrt 2250 *
          (Real.log 2250 * (Real.log 2250 - Real.log (Real.log 2250)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (72000 : ℝ) / 1000 ≤
        Real.sqrt 2311 *
          (Real.log 2311 * (Real.log 2311 - Real.log (Real.log 2311)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (72000 : ℝ) / 1000 ≤
        Real.sqrt 2381 *
          (Real.log 2381 * (Real.log 2381 - Real.log (Real.log 2381)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (72000 : ℝ) / 1000 ≤
        Real.sqrt 2441 *
          (Real.log 2441 * (Real.log 2441 - Real.log (Real.log 2441)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (72000 : ℝ) / 1000 ≤
        Real.sqrt 2521 *
          (Real.log 2521 * (Real.log 2521 - Real.log (Real.log 2521)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (72000 : ℝ) / 1000 ≤
        Real.sqrt 2585 *
          (Real.log 2585 * (Real.log 2585 - Real.log (Real.log 2585)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (72000 : ℝ) / 1000 ≤
        Real.sqrt 2640 *
          (Real.log 2640 * (Real.log 2640 - Real.log (Real.log 2640)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (72000 : ℝ) / 1000 ≤
        Real.sqrt 2687 *
          (Real.log 2687 * (Real.log 2687 - Real.log (Real.log 2687)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)

/-- The checked batch proves the Lee–Nosal psi estimate on `[1930, 2687)`. -/
theorem psi_lee_nosal_1930_2687 {x : ℝ} (ha : 1930 ≤ x) (hb : x < 2687) :
    |Chebyshev.psi x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  exact
    lee_nosal_chain_sound Chebyshev.psi_mono Chebyshev.psi_eq_psi_coe_floor (by decide +kernel)
      batch_lower batch_upper batch_a batch_b ha hb

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
