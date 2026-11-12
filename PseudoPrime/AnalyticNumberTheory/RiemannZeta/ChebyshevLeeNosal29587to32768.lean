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
  [⟨29587, 30052, 29612633, 30002876, 440000, 440000⟩,
    ⟨30052, 30442, 30002182, 30395198, 440000, 440000⟩,
    ⟨30442, 30834, 30394503, 30766724, 440000, 440000⟩,
    ⟨30834, 31206, 30766030, 31170136, 440000, 440000⟩,
    ⟨31206, 31609, 31169442, 31574241, 440000, 440000⟩,
    ⟨31609, 32013, 31573547, 31915962, 440000, 440000⟩,
    ⟨32013, 32355, 31915268, 32295114, 440000, 440000⟩,
    ⟨32355, 32734, 32294420, 32720706, 440000, 440000⟩,
    ⟨32734, 32768, 32720012, 32736649, 440000, 440000⟩]

/-- The kernel-checked prefix bounds for 29587. -/
private theorem psi_29587_bounds :
    (29612633 : ℝ) / 1000 ≤ Chebyshev.psi 29587 ∧ Chebyshev.psi 29587 ≤ (29613328 : ℝ) / 1000 := by
  have hl : 2 ^ 42722 ≤ Nat.lcmUpto 29587 := by decide +kernel
  have hu : Nat.lcmUpto 29587 ≤ 2 ^ (42722 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 30047. -/
private theorem psi_30047_bounds :
    (30002182 : ℝ) / 1000 ≤ Chebyshev.psi 30047 ∧ Chebyshev.psi 30047 ≤ (30002876 : ℝ) / 1000 := by
  have hl : 2 ^ 43284 ≤ Nat.lcmUpto 30047 := by decide +kernel
  have hu : Nat.lcmUpto 30047 ≤ 2 ^ (43284 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 30431. -/
private theorem psi_30431_bounds :
    (30394503 : ℝ) / 1000 ≤ Chebyshev.psi 30431 ∧ Chebyshev.psi 30431 ≤ (30395198 : ℝ) / 1000 := by
  have hl : 2 ^ 43850 ≤ Nat.lcmUpto 30431 := by decide +kernel
  have hu : Nat.lcmUpto 30431 ≤ 2 ^ (43850 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 30829. -/
private theorem psi_30829_bounds :
    (30766030 : ℝ) / 1000 ≤ Chebyshev.psi 30829 ∧ Chebyshev.psi 30829 ≤ (30766724 : ℝ) / 1000 := by
  have hl : 2 ^ 44386 ≤ Nat.lcmUpto 30829 := by decide +kernel
  have hu : Nat.lcmUpto 30829 ≤ 2 ^ (44386 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 31193. -/
private theorem psi_31193_bounds :
    (31169442 : ℝ) / 1000 ≤ Chebyshev.psi 31193 ∧ Chebyshev.psi 31193 ≤ (31170136 : ℝ) / 1000 := by
  have hl : 2 ^ 44968 ≤ Nat.lcmUpto 31193 := by decide +kernel
  have hu : Nat.lcmUpto 31193 ≤ 2 ^ (44968 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 31607. -/
private theorem psi_31607_bounds :
    (31573547 : ℝ) / 1000 ≤ Chebyshev.psi 31607 ∧ Chebyshev.psi 31607 ≤ (31574241 : ℝ) / 1000 := by
  have hl : 2 ^ 45551 ≤ Nat.lcmUpto 31607 := by decide +kernel
  have hu : Nat.lcmUpto 31607 ≤ 2 ^ (45551 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 32009. -/
private theorem psi_32009_bounds :
    (31915268 : ℝ) / 1000 ≤ Chebyshev.psi 32009 ∧ Chebyshev.psi 32009 ≤ (31915962 : ℝ) / 1000 := by
  have hl : 2 ^ 46044 ≤ Nat.lcmUpto 32009 := by decide +kernel
  have hu : Nat.lcmUpto 32009 ≤ 2 ^ (46044 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 32353. -/
private theorem psi_32353_bounds :
    (32294420 : ℝ) / 1000 ≤ Chebyshev.psi 32353 ∧ Chebyshev.psi 32353 ≤ (32295114 : ℝ) / 1000 := by
  have hl : 2 ^ 46591 ≤ Nat.lcmUpto 32353 := by decide +kernel
  have hu : Nat.lcmUpto 32353 ≤ 2 ^ (46591 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 32719. -/
private theorem psi_32719_bounds :
    (32720012 : ℝ) / 1000 ≤ Chebyshev.psi 32719 ∧ Chebyshev.psi 32719 ≤ (32720706 : ℝ) / 1000 := by
  have hl : 2 ^ 47205 ≤ Nat.lcmUpto 32719 := by decide +kernel
  have hu : Nat.lcmUpto 32719 ≤ 2 ^ (47205 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 32761. -/
private theorem psi_32761_bounds :
    (32735955 : ℝ) / 1000 ≤ Chebyshev.psi 32761 ∧ Chebyshev.psi 32761 ≤ (32736649 : ℝ) / 1000 := by
  have hl : 2 ^ 47228 ≤ Nat.lcmUpto 32761 := by decide +kernel
  have hu : Nat.lcmUpto 32761 ≤ 2 ^ (47228 + 1) := by decide +kernel
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
  · change (29612633 : ℝ) / 1000 ≤ Chebyshev.psi (↑(29587 : ℕ) : ℝ)
    exact psi_29587_bounds.1
  · change (30002182 : ℝ) / 1000 ≤ Chebyshev.psi (↑(30052 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 30047) (b := 30052) (by decide)
        (by decide +kernel)]
    exact psi_30047_bounds.1
  · change (30394503 : ℝ) / 1000 ≤ Chebyshev.psi (↑(30442 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 30431) (b := 30442) (by decide)
        (by decide +kernel)]
    exact psi_30431_bounds.1
  · change (30766030 : ℝ) / 1000 ≤ Chebyshev.psi (↑(30834 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 30829) (b := 30834) (by decide)
        (by decide +kernel)]
    exact psi_30829_bounds.1
  · change (31169442 : ℝ) / 1000 ≤ Chebyshev.psi (↑(31206 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 31193) (b := 31206) (by decide)
        (by decide +kernel)]
    exact psi_31193_bounds.1
  · change (31573547 : ℝ) / 1000 ≤ Chebyshev.psi (↑(31609 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 31607) (b := 31609) (by decide)
        (by decide +kernel)]
    exact psi_31607_bounds.1
  · change (31915268 : ℝ) / 1000 ≤ Chebyshev.psi (↑(32013 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 32009) (b := 32013) (by decide)
        (by decide +kernel)]
    exact psi_32009_bounds.1
  · change (32294420 : ℝ) / 1000 ≤ Chebyshev.psi (↑(32355 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 32353) (b := 32355) (by decide)
        (by decide +kernel)]
    exact psi_32353_bounds.1
  · change (32720012 : ℝ) / 1000 ≤ Chebyshev.psi (↑(32734 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 32719) (b := 32734) (by decide)
        (by decide +kernel)]
    exact psi_32719_bounds.1

/-- Every batch cell has a checked psi upper bound. -/
private theorem batch_upper :
    ∀ r ∈ batchCells, Chebyshev.psi (r.b - 1 : ℕ) ≤ (r.hi : ℝ) / 1000 := by
  intro r hr
  simp only [batchCells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change Chebyshev.psi (↑(30051 : ℕ) : ℝ) ≤ (30002876 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 30047) (b := 30051) (by decide)
        (by decide +kernel)]
    exact psi_30047_bounds.2
  · change Chebyshev.psi (↑(30441 : ℕ) : ℝ) ≤ (30395198 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 30431) (b := 30441) (by decide)
        (by decide +kernel)]
    exact psi_30431_bounds.2
  · change Chebyshev.psi (↑(30833 : ℕ) : ℝ) ≤ (30766724 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 30829) (b := 30833) (by decide)
        (by decide +kernel)]
    exact psi_30829_bounds.2
  · change Chebyshev.psi (↑(31205 : ℕ) : ℝ) ≤ (31170136 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 31193) (b := 31205) (by decide)
        (by decide +kernel)]
    exact psi_31193_bounds.2
  · change Chebyshev.psi (↑(31608 : ℕ) : ℝ) ≤ (31574241 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 31607) (b := 31608) (by decide)
        (by decide +kernel)]
    exact psi_31607_bounds.2
  · change Chebyshev.psi (↑(32012 : ℕ) : ℝ) ≤ (31915962 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 32009) (b := 32012) (by decide)
        (by decide +kernel)]
    exact psi_32009_bounds.2
  · change Chebyshev.psi (↑(32354 : ℕ) : ℝ) ≤ (32295114 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 32353) (b := 32354) (by decide)
        (by decide +kernel)]
    exact psi_32353_bounds.2
  · change Chebyshev.psi (↑(32733 : ℕ) : ℝ) ≤ (32720706 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 32719) (b := 32733) (by decide)
        (by decide +kernel)]
    exact psi_32719_bounds.2
  · change Chebyshev.psi (↑(32767 : ℕ) : ℝ) ≤ (32736649 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 32761) (b := 32767) (by decide)
        (by decide +kernel)]
    exact psi_32761_bounds.2

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
        Real.sqrt 29587 *
          (Real.log 29587 * (Real.log 29587 - Real.log (Real.log 29587)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (440000 : ℝ) / 1000 ≤
        Real.sqrt 30052 *
          (Real.log 30052 * (Real.log 30052 - Real.log (Real.log 30052)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (440000 : ℝ) / 1000 ≤
        Real.sqrt 30442 *
          (Real.log 30442 * (Real.log 30442 - Real.log (Real.log 30442)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (440000 : ℝ) / 1000 ≤
        Real.sqrt 30834 *
          (Real.log 30834 * (Real.log 30834 - Real.log (Real.log 30834)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (440000 : ℝ) / 1000 ≤
        Real.sqrt 31206 *
          (Real.log 31206 * (Real.log 31206 - Real.log (Real.log 31206)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (440000 : ℝ) / 1000 ≤
        Real.sqrt 31609 *
          (Real.log 31609 * (Real.log 31609 - Real.log (Real.log 31609)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (440000 : ℝ) / 1000 ≤
        Real.sqrt 32013 *
          (Real.log 32013 * (Real.log 32013 - Real.log (Real.log 32013)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (440000 : ℝ) / 1000 ≤
        Real.sqrt 32355 *
          (Real.log 32355 * (Real.log 32355 - Real.log (Real.log 32355)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (440000 : ℝ) / 1000 ≤
        Real.sqrt 32734 *
          (Real.log 32734 * (Real.log 32734 - Real.log (Real.log 32734)) / (8 * Real.pi))
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
        Real.sqrt 30052 *
          (Real.log 30052 * (Real.log 30052 - Real.log (Real.log 30052)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (440000 : ℝ) / 1000 ≤
        Real.sqrt 30442 *
          (Real.log 30442 * (Real.log 30442 - Real.log (Real.log 30442)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (440000 : ℝ) / 1000 ≤
        Real.sqrt 30834 *
          (Real.log 30834 * (Real.log 30834 - Real.log (Real.log 30834)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (440000 : ℝ) / 1000 ≤
        Real.sqrt 31206 *
          (Real.log 31206 * (Real.log 31206 - Real.log (Real.log 31206)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (440000 : ℝ) / 1000 ≤
        Real.sqrt 31609 *
          (Real.log 31609 * (Real.log 31609 - Real.log (Real.log 31609)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (440000 : ℝ) / 1000 ≤
        Real.sqrt 32013 *
          (Real.log 32013 * (Real.log 32013 - Real.log (Real.log 32013)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (440000 : ℝ) / 1000 ≤
        Real.sqrt 32355 *
          (Real.log 32355 * (Real.log 32355 - Real.log (Real.log 32355)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (440000 : ℝ) / 1000 ≤
        Real.sqrt 32734 *
          (Real.log 32734 * (Real.log 32734 - Real.log (Real.log 32734)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (440000 : ℝ) / 1000 ≤
        Real.sqrt 32768 *
          (Real.log 32768 * (Real.log 32768 - Real.log (Real.log 32768)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)

/-- The checked batch proves the Lee–Nosal psi estimate on `[29587, 32768)`. -/
theorem psi_lee_nosal_29587_32768 {x : ℝ} (ha : 29587 ≤ x) (hb : x < 32768) :
    |Chebyshev.psi x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  exact
    lee_nosal_chain_sound Chebyshev.psi_mono Chebyshev.psi_eq_psi_coe_floor (by decide +kernel)
      batch_lower batch_upper batch_a batch_b ha hb

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
