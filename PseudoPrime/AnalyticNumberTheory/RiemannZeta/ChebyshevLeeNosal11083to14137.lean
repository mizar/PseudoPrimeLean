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
  [⟨11083, 11347, 11077878, 11330877, 270000, 270000⟩,
    ⟨11347, 11600, 11330183, 11578331, 270000, 270000⟩,
    ⟨11600, 11847, 11577637, 11812615, 270000, 270000⟩,
    ⟨11847, 12081, 11811921, 12051751, 270000, 270000⟩,
    ⟨12081, 12321, 12051056, 12290193, 270000, 270000⟩,
    ⟨12321, 12559, 12289499, 12563986, 270000, 270000⟩,
    ⟨12559, 12821, 12563292, 12823916, 270000, 270000⟩,
    ⟨12821, 13063, 12832233, 13088699, 270000, 270000⟩,
    ⟨13063, 13313, 13097709, 13325755, 270000, 270000⟩,
    ⟨13313, 13597, 13334765, 13582913, 270000, 270000⟩,
    ⟨13597, 13859, 13591229, 13858785, 270000, 270000⟩,
    ⟨13859, 14137, 13867795, 14116636, 270000, 270000⟩]

/-- The kernel-checked prefix bounds for 11083. -/
private theorem psi_11083_bounds :
    (11077878 : ℝ) / 1000 ≤ Chebyshev.psi 11083 ∧ Chebyshev.psi 11083 ≤ (11078572 : ℝ) / 1000 := by
  have hl : 2 ^ 15982 ≤ Nat.lcmUpto 11083 := by decide +kernel
  have hu : Nat.lcmUpto 11083 ≤ 2 ^ (15982 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 11329. -/
private theorem psi_11329_bounds :
    (11330183 : ℝ) / 1000 ≤ Chebyshev.psi 11329 ∧ Chebyshev.psi 11329 ≤ (11330877 : ℝ) / 1000 := by
  have hl : 2 ^ 16346 ≤ Nat.lcmUpto 11329 := by decide +kernel
  have hu : Nat.lcmUpto 11329 ≤ 2 ^ (16346 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 11597. -/
private theorem psi_11597_bounds :
    (11577637 : ℝ) / 1000 ≤ Chebyshev.psi 11597 ∧ Chebyshev.psi 11597 ≤ (11578331 : ℝ) / 1000 := by
  have hl : 2 ^ 16703 ≤ Nat.lcmUpto 11597 := by decide +kernel
  have hu : Nat.lcmUpto 11597 ≤ 2 ^ (16703 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 11839. -/
private theorem psi_11839_bounds :
    (11811921 : ℝ) / 1000 ≤ Chebyshev.psi 11839 ∧ Chebyshev.psi 11839 ≤ (11812615 : ℝ) / 1000 := by
  have hl : 2 ^ 17041 ≤ Nat.lcmUpto 11839 := by decide +kernel
  have hu : Nat.lcmUpto 11839 ≤ 2 ^ (17041 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 12073. -/
private theorem psi_12073_bounds :
    (12051056 : ℝ) / 1000 ≤ Chebyshev.psi 12073 ∧ Chebyshev.psi 12073 ≤ (12051751 : ℝ) / 1000 := by
  have hl : 2 ^ 17386 ≤ Nat.lcmUpto 12073 := by decide +kernel
  have hu : Nat.lcmUpto 12073 ≤ 2 ^ (17386 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 12301. -/
private theorem psi_12301_bounds :
    (12289499 : ℝ) / 1000 ≤ Chebyshev.psi 12301 ∧ Chebyshev.psi 12301 ≤ (12290193 : ℝ) / 1000 := by
  have hl : 2 ^ 17730 ≤ Nat.lcmUpto 12301 := by decide +kernel
  have hu : Nat.lcmUpto 12301 ≤ 2 ^ (17730 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 12553. -/
private theorem psi_12553_bounds :
    (12563292 : ℝ) / 1000 ≤ Chebyshev.psi 12553 ∧ Chebyshev.psi 12553 ≤ (12563986 : ℝ) / 1000 := by
  have hl : 2 ^ 18125 ≤ Nat.lcmUpto 12553 := by decide +kernel
  have hu : Nat.lcmUpto 12553 ≤ 2 ^ (18125 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 12809. -/
private theorem psi_12809_bounds :
    (12823222 : ℝ) / 1000 ≤ Chebyshev.psi 12809 ∧ Chebyshev.psi 12809 ≤ (12823916 : ℝ) / 1000 := by
  have hl : 2 ^ 18500 ≤ Nat.lcmUpto 12809 := by decide +kernel
  have hu : Nat.lcmUpto 12809 ≤ 2 ^ (18500 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 12821. -/
private theorem psi_12821_bounds :
    (12832233 : ℝ) / 1000 ≤ Chebyshev.psi 12821 ∧ Chebyshev.psi 12821 ≤ (12832927 : ℝ) / 1000 := by
  have hl : 2 ^ 18513 ≤ Nat.lcmUpto 12821 := by decide +kernel
  have hu : Nat.lcmUpto 12821 ≤ 2 ^ (18513 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 13049. -/
private theorem psi_13049_bounds :
    (13088005 : ℝ) / 1000 ≤ Chebyshev.psi 13049 ∧ Chebyshev.psi 13049 ≤ (13088699 : ℝ) / 1000 := by
  have hl : 2 ^ 18882 ≤ Nat.lcmUpto 13049 := by decide +kernel
  have hu : Nat.lcmUpto 13049 ≤ 2 ^ (18882 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 13063. -/
private theorem psi_13063_bounds :
    (13097709 : ℝ) / 1000 ≤ Chebyshev.psi 13063 ∧ Chebyshev.psi 13063 ≤ (13098403 : ℝ) / 1000 := by
  have hl : 2 ^ 18896 ≤ Nat.lcmUpto 13063 := by decide +kernel
  have hu : Nat.lcmUpto 13063 ≤ 2 ^ (18896 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 13309. -/
private theorem psi_13309_bounds :
    (13325061 : ℝ) / 1000 ≤ Chebyshev.psi 13309 ∧ Chebyshev.psi 13309 ≤ (13325755 : ℝ) / 1000 := by
  have hl : 2 ^ 19224 ≤ Nat.lcmUpto 13309 := by decide +kernel
  have hu : Nat.lcmUpto 13309 ≤ 2 ^ (19224 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 13313. -/
private theorem psi_13313_bounds :
    (13334765 : ℝ) / 1000 ≤ Chebyshev.psi 13313 ∧ Chebyshev.psi 13313 ≤ (13335459 : ℝ) / 1000 := by
  have hl : 2 ^ 19238 ≤ Nat.lcmUpto 13313 := by decide +kernel
  have hu : Nat.lcmUpto 13313 ≤ 2 ^ (19238 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 13591. -/
private theorem psi_13591_bounds :
    (13582218 : ℝ) / 1000 ≤ Chebyshev.psi 13591 ∧ Chebyshev.psi 13591 ≤ (13582913 : ℝ) / 1000 := by
  have hl : 2 ^ 19595 ≤ Nat.lcmUpto 13591 := by decide +kernel
  have hu : Nat.lcmUpto 13591 ≤ 2 ^ (19595 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 13597. -/
private theorem psi_13597_bounds :
    (13591229 : ℝ) / 1000 ≤ Chebyshev.psi 13597 ∧ Chebyshev.psi 13597 ≤ (13591924 : ℝ) / 1000 := by
  have hl : 2 ^ 19608 ≤ Nat.lcmUpto 13597 := by decide +kernel
  have hu : Nat.lcmUpto 13597 ≤ 2 ^ (19608 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 13841. -/
private theorem psi_13841_bounds :
    (13858091 : ℝ) / 1000 ≤ Chebyshev.psi 13841 ∧ Chebyshev.psi 13841 ≤ (13858785 : ℝ) / 1000 := by
  have hl : 2 ^ 19993 ≤ Nat.lcmUpto 13841 := by decide +kernel
  have hu : Nat.lcmUpto 13841 ≤ 2 ^ (19993 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 13859. -/
private theorem psi_13859_bounds :
    (13867795 : ℝ) / 1000 ≤ Chebyshev.psi 13859 ∧ Chebyshev.psi 13859 ≤ (13868489 : ℝ) / 1000 := by
  have hl : 2 ^ 20007 ≤ Nat.lcmUpto 13859 := by decide +kernel
  have hu : Nat.lcmUpto 13859 ≤ 2 ^ (20007 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The kernel-checked prefix bounds for 14107. -/
private theorem psi_14107_bounds :
    (14115942 : ℝ) / 1000 ≤ Chebyshev.psi 14107 ∧ Chebyshev.psi 14107 ≤ (14116636 : ℝ) / 1000 := by
  have hl : 2 ^ 20365 ≤ Nat.lcmUpto 14107 := by decide +kernel
  have hu : Nat.lcmUpto 14107 ≤ 2 ^ (20365 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- A rational certificate bounds the envelope from 11083 onward. -/
private theorem batch_envelope {t : ℝ} (ht : 11083 ≤ t) :
    (270 : ℝ) ≤
      Real.sqrt t * (Real.log t * (Real.log t - Real.log (Real.log t)) / (8 * Real.pi)) := by
  have h :=
    lee_nosal_envelope_of_log_checks (N := 11083) (lo := 931 / 100) (hi := 932 / 100) (vlo :=
      223 / 100) (vhi := 224 / 100) (c := 270) (j := 14) (k := 4) (n := 32) (m := 32)
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by decide +kernel) (by decide +kernel) (by norm_num only)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact
    h.trans
      (lee_nosal_envelope_mono (x := 11083) (y := t)
        (Real.exp_one_lt_three.le.trans (by norm_num only)) ht)

/-- Every batch cell has a checked psi lower bound. -/
private theorem batch_lower : ∀ r ∈ batchCells, (r.lo : ℝ) / 1000 ≤ Chebyshev.psi r.a := by
  intro r hr
  simp only [batchCells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change (11077878 : ℝ) / 1000 ≤ Chebyshev.psi (↑(11083 : ℕ) : ℝ)
    exact psi_11083_bounds.1
  · change (11330183 : ℝ) / 1000 ≤ Chebyshev.psi (↑(11347 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 11329) (b := 11347) (by decide)
        (by decide +kernel)]
    exact psi_11329_bounds.1
  · change (11577637 : ℝ) / 1000 ≤ Chebyshev.psi (↑(11600 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 11597) (b := 11600) (by decide)
        (by decide +kernel)]
    exact psi_11597_bounds.1
  · change (11811921 : ℝ) / 1000 ≤ Chebyshev.psi (↑(11847 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 11839) (b := 11847) (by decide)
        (by decide +kernel)]
    exact psi_11839_bounds.1
  · change (12051056 : ℝ) / 1000 ≤ Chebyshev.psi (↑(12081 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 12073) (b := 12081) (by decide)
        (by decide +kernel)]
    exact psi_12073_bounds.1
  · change (12289499 : ℝ) / 1000 ≤ Chebyshev.psi (↑(12321 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 12301) (b := 12321) (by decide)
        (by decide +kernel)]
    exact psi_12301_bounds.1
  · change (12563292 : ℝ) / 1000 ≤ Chebyshev.psi (↑(12559 : ℕ) : ℝ)
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 12553) (b := 12559) (by decide)
        (by decide +kernel)]
    exact psi_12553_bounds.1
  · change (12832233 : ℝ) / 1000 ≤ Chebyshev.psi (↑(12821 : ℕ) : ℝ)
    exact psi_12821_bounds.1
  · change (13097709 : ℝ) / 1000 ≤ Chebyshev.psi (↑(13063 : ℕ) : ℝ)
    exact psi_13063_bounds.1
  · change (13334765 : ℝ) / 1000 ≤ Chebyshev.psi (↑(13313 : ℕ) : ℝ)
    exact psi_13313_bounds.1
  · change (13591229 : ℝ) / 1000 ≤ Chebyshev.psi (↑(13597 : ℕ) : ℝ)
    exact psi_13597_bounds.1
  · change (13867795 : ℝ) / 1000 ≤ Chebyshev.psi (↑(13859 : ℕ) : ℝ)
    exact psi_13859_bounds.1

/-- Every batch cell has a checked psi upper bound. -/
private theorem batch_upper :
    ∀ r ∈ batchCells, Chebyshev.psi (r.b - 1 : ℕ) ≤ (r.hi : ℝ) / 1000 := by
  intro r hr
  simp only [batchCells, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change Chebyshev.psi (↑(11346 : ℕ) : ℝ) ≤ (11330877 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 11329) (b := 11346) (by decide)
        (by decide +kernel)]
    exact psi_11329_bounds.2
  · change Chebyshev.psi (↑(11599 : ℕ) : ℝ) ≤ (11578331 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 11597) (b := 11599) (by decide)
        (by decide +kernel)]
    exact psi_11597_bounds.2
  · change Chebyshev.psi (↑(11846 : ℕ) : ℝ) ≤ (11812615 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 11839) (b := 11846) (by decide)
        (by decide +kernel)]
    exact psi_11839_bounds.2
  · change Chebyshev.psi (↑(12080 : ℕ) : ℝ) ≤ (12051751 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 12073) (b := 12080) (by decide)
        (by decide +kernel)]
    exact psi_12073_bounds.2
  · change Chebyshev.psi (↑(12320 : ℕ) : ℝ) ≤ (12290193 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 12301) (b := 12320) (by decide)
        (by decide +kernel)]
    exact psi_12301_bounds.2
  · change Chebyshev.psi (↑(12558 : ℕ) : ℝ) ≤ (12563986 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 12553) (b := 12558) (by decide)
        (by decide +kernel)]
    exact psi_12553_bounds.2
  · change Chebyshev.psi (↑(12820 : ℕ) : ℝ) ≤ (12823916 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 12809) (b := 12820) (by decide)
        (by decide +kernel)]
    exact psi_12809_bounds.2
  · change Chebyshev.psi (↑(13062 : ℕ) : ℝ) ≤ (13088699 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 13049) (b := 13062) (by decide)
        (by decide +kernel)]
    exact psi_13049_bounds.2
  · change Chebyshev.psi (↑(13312 : ℕ) : ℝ) ≤ (13325755 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 13309) (b := 13312) (by decide)
        (by decide +kernel)]
    exact psi_13309_bounds.2
  · change Chebyshev.psi (↑(13596 : ℕ) : ℝ) ≤ (13582913 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 13591) (b := 13596) (by decide)
        (by decide +kernel)]
    exact psi_13591_bounds.2
  · change Chebyshev.psi (↑(13858 : ℕ) : ℝ) ≤ (13858785 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 13841) (b := 13858) (by decide)
        (by decide +kernel)]
    exact psi_13841_bounds.2
  · change Chebyshev.psi (↑(14136 : ℕ) : ℝ) ≤ (14116636 : ℝ) / 1000
    rw [Arithmetic.psi_eq_of_no_prime_power (a := 14107) (b := 14136) (by decide)
        (by decide +kernel)]
    exact psi_14107_bounds.2

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
      (270000 : ℝ) / 1000 ≤
        Real.sqrt 11083 *
          (Real.log 11083 * (Real.log 11083 - Real.log (Real.log 11083)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (270000 : ℝ) / 1000 ≤
        Real.sqrt 11347 *
          (Real.log 11347 * (Real.log 11347 - Real.log (Real.log 11347)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (270000 : ℝ) / 1000 ≤
        Real.sqrt 11600 *
          (Real.log 11600 * (Real.log 11600 - Real.log (Real.log 11600)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (270000 : ℝ) / 1000 ≤
        Real.sqrt 11847 *
          (Real.log 11847 * (Real.log 11847 - Real.log (Real.log 11847)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (270000 : ℝ) / 1000 ≤
        Real.sqrt 12081 *
          (Real.log 12081 * (Real.log 12081 - Real.log (Real.log 12081)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (270000 : ℝ) / 1000 ≤
        Real.sqrt 12321 *
          (Real.log 12321 * (Real.log 12321 - Real.log (Real.log 12321)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (270000 : ℝ) / 1000 ≤
        Real.sqrt 12559 *
          (Real.log 12559 * (Real.log 12559 - Real.log (Real.log 12559)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (270000 : ℝ) / 1000 ≤
        Real.sqrt 12821 *
          (Real.log 12821 * (Real.log 12821 - Real.log (Real.log 12821)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (270000 : ℝ) / 1000 ≤
        Real.sqrt 13063 *
          (Real.log 13063 * (Real.log 13063 - Real.log (Real.log 13063)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (270000 : ℝ) / 1000 ≤
        Real.sqrt 13313 *
          (Real.log 13313 * (Real.log 13313 - Real.log (Real.log 13313)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (270000 : ℝ) / 1000 ≤
        Real.sqrt 13597 *
          (Real.log 13597 * (Real.log 13597 - Real.log (Real.log 13597)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (270000 : ℝ) / 1000 ≤
        Real.sqrt 13859 *
          (Real.log 13859 * (Real.log 13859 - Real.log (Real.log 13859)) / (8 * Real.pi))
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
      (270000 : ℝ) / 1000 ≤
        Real.sqrt 11347 *
          (Real.log 11347 * (Real.log 11347 - Real.log (Real.log 11347)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (270000 : ℝ) / 1000 ≤
        Real.sqrt 11600 *
          (Real.log 11600 * (Real.log 11600 - Real.log (Real.log 11600)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (270000 : ℝ) / 1000 ≤
        Real.sqrt 11847 *
          (Real.log 11847 * (Real.log 11847 - Real.log (Real.log 11847)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (270000 : ℝ) / 1000 ≤
        Real.sqrt 12081 *
          (Real.log 12081 * (Real.log 12081 - Real.log (Real.log 12081)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (270000 : ℝ) / 1000 ≤
        Real.sqrt 12321 *
          (Real.log 12321 * (Real.log 12321 - Real.log (Real.log 12321)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (270000 : ℝ) / 1000 ≤
        Real.sqrt 12559 *
          (Real.log 12559 * (Real.log 12559 - Real.log (Real.log 12559)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (270000 : ℝ) / 1000 ≤
        Real.sqrt 12821 *
          (Real.log 12821 * (Real.log 12821 - Real.log (Real.log 12821)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (270000 : ℝ) / 1000 ≤
        Real.sqrt 13063 *
          (Real.log 13063 * (Real.log 13063 - Real.log (Real.log 13063)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (270000 : ℝ) / 1000 ≤
        Real.sqrt 13313 *
          (Real.log 13313 * (Real.log 13313 - Real.log (Real.log 13313)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (270000 : ℝ) / 1000 ≤
        Real.sqrt 13597 *
          (Real.log 13597 * (Real.log 13597 - Real.log (Real.log 13597)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (270000 : ℝ) / 1000 ≤
        Real.sqrt 13859 *
          (Real.log 13859 * (Real.log 13859 - Real.log (Real.log 13859)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)
  · change
      (270000 : ℝ) / 1000 ≤
        Real.sqrt 14137 *
          (Real.log 14137 * (Real.log 14137 - Real.log (Real.log 14137)) / (8 * Real.pi))
    norm_num only
    exact batch_envelope (by norm_num only)

/-- The checked batch proves the Lee–Nosal psi estimate on `[11083, 14137)`. -/
theorem psi_lee_nosal_11083_14137 {x : ℝ} (ha : 11083 ≤ x) (hb : x < 14137) :
    |Chebyshev.psi x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  exact
    lee_nosal_chain_sound Chebyshev.psi_mono Chebyshev.psi_eq_psi_coe_floor (by decide +kernel)
      batch_lower batch_upper batch_a batch_b ha hb

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
