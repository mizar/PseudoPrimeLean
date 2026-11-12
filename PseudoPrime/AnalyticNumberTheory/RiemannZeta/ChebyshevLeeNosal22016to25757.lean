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
  [⟨22016, 22446, 22006729, 22452424, 440000, 440000⟩,
    ⟨22446, 22861, 22451730, 22878709, 440000, 440000⟩,
    ⟨22861, 23279, 22888413, 23300836, 440000, 440000⟩,
    ⟨23279, 23687, 23309846, 23713259, 440000, 440000⟩,
    ⟨23687, 24071, 23722962, 24126374, 440000, 440000⟩,
    ⟨24071, 24443, 24136077, 24503446, 440000, 440000⟩,
    ⟨24443, 24889, 24513150, 24882598, 440000, 440000⟩,
    ⟨24889, 25332, 24892301, 25318588, 440000, 440000⟩,
    ⟨25332, 25757, 25317893, 25744873, 440000, 440000⟩]

/-- The kernel-checked prefix bounds for 22013. -/
private theorem psi_22013_bounds :
    (22006729 : ℝ) / 1000 ≤ Chebyshev.psi 22013 ∧ Chebyshev.psi 22013 ≤ (22007423 : ℝ) / 1000 := by
  have hl : 2 ^ 31749 ≤ Nat.lcmUpto 22013 := by decide +kernel
  have hu : Nat.lcmUpto 22013 ≤ 2 ^ (31749 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 22441. -/
private theorem psi_22441_bounds :
    (22451730 : ℝ) / 1000 ≤ Chebyshev.psi 22441 ∧ Chebyshev.psi 22441 ≤ (22452424 : ℝ) / 1000 := by
  have hl : 2 ^ 32391 ≤ Nat.lcmUpto 22441 := by decide +kernel
  have hu : Nat.lcmUpto 22441 ≤ 2 ^ (32391 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 22859. -/
private theorem psi_22859_bounds :
    (22878015 : ℝ) / 1000 ≤ Chebyshev.psi 22859 ∧ Chebyshev.psi 22859 ≤ (22878709 : ℝ) / 1000 := by
  have hl : 2 ^ 33006 ≤ Nat.lcmUpto 22859 := by decide +kernel
  have hu : Nat.lcmUpto 22859 ≤ 2 ^ (33006 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 22861. -/
private theorem psi_22861_bounds :
    (22888413 : ℝ) / 1000 ≤ Chebyshev.psi 22861 ∧ Chebyshev.psi 22861 ≤ (22889107 : ℝ) / 1000 := by
  have hl : 2 ^ 33021 ≤ Nat.lcmUpto 22861 := by decide +kernel
  have hu : Nat.lcmUpto 22861 ≤ 2 ^ (33021 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 23269. -/
private theorem psi_23269_bounds :
    (23300142 : ℝ) / 1000 ≤ Chebyshev.psi 23269 ∧ Chebyshev.psi 23269 ≤ (23300836 : ℝ) / 1000 := by
  have hl : 2 ^ 33615 ≤ Nat.lcmUpto 23269 := by decide +kernel
  have hu : Nat.lcmUpto 23269 ≤ 2 ^ (33615 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 23279. -/
private theorem psi_23279_bounds :
    (23309846 : ℝ) / 1000 ≤ Chebyshev.psi 23279 ∧ Chebyshev.psi 23279 ≤ (23310540 : ℝ) / 1000 := by
  have hl : 2 ^ 33629 ≤ Nat.lcmUpto 23279 := by decide +kernel
  have hu : Nat.lcmUpto 23279 ≤ 2 ^ (33629 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 23677. -/
private theorem psi_23677_bounds :
    (23712565 : ℝ) / 1000 ≤ Chebyshev.psi 23677 ∧ Chebyshev.psi 23677 ≤ (23713259 : ℝ) / 1000 := by
  have hl : 2 ^ 34210 ≤ Nat.lcmUpto 23677 := by decide +kernel
  have hu : Nat.lcmUpto 23677 ≤ 2 ^ (34210 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 23687. -/
private theorem psi_23687_bounds :
    (23722962 : ℝ) / 1000 ≤ Chebyshev.psi 23687 ∧ Chebyshev.psi 23687 ≤ (23723656 : ℝ) / 1000 := by
  have hl : 2 ^ 34225 ≤ Nat.lcmUpto 23687 := by decide +kernel
  have hu : Nat.lcmUpto 23687 ≤ 2 ^ (34225 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 24061. -/
private theorem psi_24061_bounds :
    (24125680 : ℝ) / 1000 ≤ Chebyshev.psi 24061 ∧ Chebyshev.psi 24061 ≤ (24126374 : ℝ) / 1000 := by
  have hl : 2 ^ 34806 ≤ Nat.lcmUpto 24061 := by decide +kernel
  have hu : Nat.lcmUpto 24061 ≤ 2 ^ (34806 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 24071. -/
private theorem psi_24071_bounds :
    (24136077 : ℝ) / 1000 ≤ Chebyshev.psi 24071 ∧ Chebyshev.psi 24071 ≤ (24136772 : ℝ) / 1000 := by
  have hl : 2 ^ 34821 ≤ Nat.lcmUpto 24071 := by decide +kernel
  have hu : Nat.lcmUpto 24071 ≤ 2 ^ (34821 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 24439. -/
private theorem psi_24439_bounds :
    (24502752 : ℝ) / 1000 ≤ Chebyshev.psi 24439 ∧ Chebyshev.psi 24439 ≤ (24503446 : ℝ) / 1000 := by
  have hl : 2 ^ 35350 ≤ Nat.lcmUpto 24439 := by decide +kernel
  have hu : Nat.lcmUpto 24439 ≤ 2 ^ (35350 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 24443. -/
private theorem psi_24443_bounds :
    (24513150 : ℝ) / 1000 ≤ Chebyshev.psi 24443 ∧ Chebyshev.psi 24443 ≤ (24513844 : ℝ) / 1000 := by
  have hl : 2 ^ 35365 ≤ Nat.lcmUpto 24443 := by decide +kernel
  have hu : Nat.lcmUpto 24443 ≤ 2 ^ (35365 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 24877. -/
private theorem psi_24877_bounds :
    (24881904 : ℝ) / 1000 ≤ Chebyshev.psi 24877 ∧ Chebyshev.psi 24877 ≤ (24882598 : ℝ) / 1000 := by
  have hl : 2 ^ 35897 ≤ Nat.lcmUpto 24877 := by decide +kernel
  have hu : Nat.lcmUpto 24877 ≤ 2 ^ (35897 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 24889. -/
private theorem psi_24889_bounds :
    (24892301 : ℝ) / 1000 ≤ Chebyshev.psi 24889 ∧ Chebyshev.psi 24889 ≤ (24892995 : ℝ) / 1000 := by
  have hl : 2 ^ 35912 ≤ Nat.lcmUpto 24889 := by decide +kernel
  have hu : Nat.lcmUpto 24889 ≤ 2 ^ (35912 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 25321. -/
private theorem psi_25321_bounds :
    (25317893 : ℝ) / 1000 ≤ Chebyshev.psi 25321 ∧ Chebyshev.psi 25321 ≤ (25318588 : ℝ) / 1000 := by
  have hl : 2 ^ 36526 ≤ Nat.lcmUpto 25321 := by decide +kernel
  have hu : Nat.lcmUpto 25321 ≤ 2 ^ (36526 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 25747. -/
private theorem psi_25747_bounds :
    (25744179 : ℝ) / 1000 ≤ Chebyshev.psi 25747 ∧ Chebyshev.psi 25747 ≤ (25744873 : ℝ) / 1000 := by
  have hl : 2 ^ 37141 ≤ Nat.lcmUpto 25747 := by decide +kernel
  have hu : Nat.lcmUpto 25747 ≤ 2 ^ (37141 + 1) := by decide +kernel
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
  · change (22006729 : ℝ) / 1000 ≤ Chebyshev.psi (↑(22016 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 22013) (b := 22016) (by decide)
        (by decide +kernel)]
    exact psi_22013_bounds.1
  · change (22451730 : ℝ) / 1000 ≤ Chebyshev.psi (↑(22446 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 22441) (b := 22446) (by decide)
        (by decide +kernel)]
    exact psi_22441_bounds.1
  · change (22888413 : ℝ) / 1000 ≤ Chebyshev.psi (↑(22861 : ℕ) : ℝ)
    exact psi_22861_bounds.1
  · change (23309846 : ℝ) / 1000 ≤ Chebyshev.psi (↑(23279 : ℕ) : ℝ)
    exact psi_23279_bounds.1
  · change (23722962 : ℝ) / 1000 ≤ Chebyshev.psi (↑(23687 : ℕ) : ℝ)
    exact psi_23687_bounds.1
  · change (24136077 : ℝ) / 1000 ≤ Chebyshev.psi (↑(24071 : ℕ) : ℝ)
    exact psi_24071_bounds.1
  · change (24513150 : ℝ) / 1000 ≤ Chebyshev.psi (↑(24443 : ℕ) : ℝ)
    exact psi_24443_bounds.1
  · change (24892301 : ℝ) / 1000 ≤ Chebyshev.psi (↑(24889 : ℕ) : ℝ)
    exact psi_24889_bounds.1
  · change (25317893 : ℝ) / 1000 ≤ Chebyshev.psi (↑(25332 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 25321) (b := 25332) (by decide)
        (by decide +kernel)]
    exact psi_25321_bounds.1

/-- Every batch cell has a checked psi upper bound. -/
private theorem batch_upper :
    ∀ r ∈ batchCells, Chebyshev.psi (r.b - 1 : ℕ) ≤ (r.hi : ℝ) / 1000 := by
  intro r hr
  simp only [batchCells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change Chebyshev.psi (↑(22445 : ℕ) : ℝ) ≤ (22452424 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 22441) (b := 22445) (by decide)
        (by decide +kernel)]
    exact psi_22441_bounds.2
  · change Chebyshev.psi (↑(22860 : ℕ) : ℝ) ≤ (22878709 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 22859) (b := 22860) (by decide)
        (by decide +kernel)]
    exact psi_22859_bounds.2
  · change Chebyshev.psi (↑(23278 : ℕ) : ℝ) ≤ (23300836 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 23269) (b := 23278) (by decide)
        (by decide +kernel)]
    exact psi_23269_bounds.2
  · change Chebyshev.psi (↑(23686 : ℕ) : ℝ) ≤ (23713259 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 23677) (b := 23686) (by decide)
        (by decide +kernel)]
    exact psi_23677_bounds.2
  · change Chebyshev.psi (↑(24070 : ℕ) : ℝ) ≤ (24126374 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 24061) (b := 24070) (by decide)
        (by decide +kernel)]
    exact psi_24061_bounds.2
  · change Chebyshev.psi (↑(24442 : ℕ) : ℝ) ≤ (24503446 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 24439) (b := 24442) (by decide)
        (by decide +kernel)]
    exact psi_24439_bounds.2
  · change Chebyshev.psi (↑(24888 : ℕ) : ℝ) ≤ (24882598 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 24877) (b := 24888) (by decide)
        (by decide +kernel)]
    exact psi_24877_bounds.2
  · change Chebyshev.psi (↑(25331 : ℕ) : ℝ) ≤ (25318588 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 25321) (b := 25331) (by decide)
        (by decide +kernel)]
    exact psi_25321_bounds.2
  · change Chebyshev.psi (↑(25756 : ℕ) : ℝ) ≤ (25744873 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 25747) (b := 25756) (by decide)
        (by decide +kernel)]
    exact psi_25747_bounds.2

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
        Real.sqrt 22016 *
          (Real.log 22016 * (Real.log 22016 - Real.log (Real.log 22016)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (440000 : ℝ) / 1000 ≤
        Real.sqrt 22446 *
          (Real.log 22446 * (Real.log 22446 - Real.log (Real.log 22446)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (440000 : ℝ) / 1000 ≤
        Real.sqrt 22861 *
          (Real.log 22861 * (Real.log 22861 - Real.log (Real.log 22861)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (440000 : ℝ) / 1000 ≤
        Real.sqrt 23279 *
          (Real.log 23279 * (Real.log 23279 - Real.log (Real.log 23279)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (440000 : ℝ) / 1000 ≤
        Real.sqrt 23687 *
          (Real.log 23687 * (Real.log 23687 - Real.log (Real.log 23687)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (440000 : ℝ) / 1000 ≤
        Real.sqrt 24071 *
          (Real.log 24071 * (Real.log 24071 - Real.log (Real.log 24071)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (440000 : ℝ) / 1000 ≤
        Real.sqrt 24443 *
          (Real.log 24443 * (Real.log 24443 - Real.log (Real.log 24443)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (440000 : ℝ) / 1000 ≤
        Real.sqrt 24889 *
          (Real.log 24889 * (Real.log 24889 - Real.log (Real.log 24889)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (440000 : ℝ) / 1000 ≤
        Real.sqrt 25332 *
          (Real.log 25332 * (Real.log 25332 - Real.log (Real.log 25332)) / (8 * Real.pi))
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
        Real.sqrt 22446 *
          (Real.log 22446 * (Real.log 22446 - Real.log (Real.log 22446)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (440000 : ℝ) / 1000 ≤
        Real.sqrt 22861 *
          (Real.log 22861 * (Real.log 22861 - Real.log (Real.log 22861)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (440000 : ℝ) / 1000 ≤
        Real.sqrt 23279 *
          (Real.log 23279 * (Real.log 23279 - Real.log (Real.log 23279)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (440000 : ℝ) / 1000 ≤
        Real.sqrt 23687 *
          (Real.log 23687 * (Real.log 23687 - Real.log (Real.log 23687)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (440000 : ℝ) / 1000 ≤
        Real.sqrt 24071 *
          (Real.log 24071 * (Real.log 24071 - Real.log (Real.log 24071)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (440000 : ℝ) / 1000 ≤
        Real.sqrt 24443 *
          (Real.log 24443 * (Real.log 24443 - Real.log (Real.log 24443)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (440000 : ℝ) / 1000 ≤
        Real.sqrt 24889 *
          (Real.log 24889 * (Real.log 24889 - Real.log (Real.log 24889)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (440000 : ℝ) / 1000 ≤
        Real.sqrt 25332 *
          (Real.log 25332 * (Real.log 25332 - Real.log (Real.log 25332)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (440000 : ℝ) / 1000 ≤
        Real.sqrt 25757 *
          (Real.log 25757 * (Real.log 25757 - Real.log (Real.log 25757)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)

/-- The checked batch proves the Lee–Nosal psi estimate on `[22016, 25757)`. -/
theorem psi_lee_nosal_22016_25757 {x : ℝ} (ha : 22016 ≤ x) (hb : x < 25757) :
    |Chebyshev.psi x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  exact
    lee_nosal_chain_sound Chebyshev.psi_mono Chebyshev.psi_eq_psi_coe_floor (by decide +kernel)
      batch_lower batch_upper batch_a batch_b ha hb

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
