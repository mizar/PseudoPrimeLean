/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ExponentialRampCutoff

/-! # Signed local corrections for the exponential ramp

Local value and parity determine which prime powers contribute positive deficits.
The cutoff tail remains nonpositive.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The signed local term is 2W(u)-Re(1+c^k)exp(-u), for local value c and power k.
It retains negative contributions outside the cutoff rather than taking absolute values.
These terms compare the ramp sum with the two primitive Gamma sums. -/
noncomputable def exponentialRampLocalCorrection (c : ℂ) (u : ℝ) (k : ℕ) : ℝ :=
  2 * exponentialRampWeight u - (1 + c ^ k).re * Real.exp (-u)

/-- At nonnegative u the ramp weight is at most one. Compare with exp(-u).
This supplies the compact contribution to signed local prime-power costs. -/
theorem exponentialRampWeight_le_one {u : ℝ} (hu : 0 ≤ u) : exponentialRampWeight u ≤ 1 :=
  (exponentialRampWeight_bounds u).2.trans (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hu))

/-- For local value zero and positive power, the signed term is at most one.
Use W≤exp(-u) and W≤1; ramified primes pay one copy per retained power. -/
theorem exponentialRampLocalCorrection_zero {u : ℝ} (hu : 0 ≤ u) {k : ℕ} (hk : 0 < k) :
    exponentialRampLocalCorrection 0 u k ≤ 1 := by
  simp only [exponentialRampLocalCorrection, zero_pow hk.ne', add_zero, Complex.one_re, one_mul]
  linarith only [(exponentialRampWeight_bounds u).2, exponentialRampWeight_le_one hu]

/-- For local value one the signed term is nonpositive at every height and power.
Use W≤exp(-u), so unramified value-one primes create no positive deficit. -/
theorem exponentialRampLocalCorrection_one (u : ℝ) (k : ℕ) :
    exponentialRampLocalCorrection 1 u k ≤ 0 := by
  simp only [exponentialRampLocalCorrection, one_pow, Complex.add_re, Complex.one_re]
  linarith only [(exponentialRampWeight_bounds u).2]

/-- For local value minus one at even power, the signed correction is nonpositive.
The power equals one, so the exponential comparison removes the term. -/
theorem exponentialRampLocalCorrection_neg_one_even (u : ℝ) {k : ℕ} (hk : Even k) :
    exponentialRampLocalCorrection (-1) u k ≤ 0 := by
  simp only [exponentialRampLocalCorrection, hk.neg_one_pow, Complex.add_re, Complex.one_re]
  linarith only [(exponentialRampWeight_bounds u).2]

/-- For local value minus one at odd power and nonnegative height, the term is at most two.
The character contributions cancel, leaving twice the ramp weight. -/
theorem exponentialRampLocalCorrection_neg_one_odd {u : ℝ} (hu : 0 ≤ u) {k : ℕ} (hk : Odd k) :
    exponentialRampLocalCorrection (-1) u k ≤ 2 := by
  simp only [exponentialRampLocalCorrection, hk.neg_one_pow, add_neg_cancel, Complex.zero_re,
    zero_mul, sub_zero]
  linarith only [exponentialRampWeight_le_one hu]

/-- For local value zero, one or minus one, Re(1+c^k) is nonnegative at every power.
Split the local values and power parity to justify dropping the cutoff tail. -/
theorem quadratic_one_add_pow_re_nonneg {c : ℂ} (hc : c = 0 ∨ c = 1 ∨ c = -1) (k : ℕ) :
    0 ≤ (1 + c ^ k).re := by
  rcases hc with rfl | rfl | rfl
  · by_cases hk : k = 0
    · simp only [hk, pow_zero, Complex.add_re, Complex.one_re]
      norm_num only
    · simp only [zero_pow hk, add_zero, Complex.one_re]
      norm_num only
  · simp only [one_pow, Complex.add_re, Complex.one_re]
    norm_num only
  · rcases Nat.even_or_odd k with hk | hk
    · simp only [hk.neg_one_pow, Complex.add_re, Complex.one_re]
      norm_num only
    · simp only [hk.neg_one_pow, add_neg_cancel, Complex.zero_re, le_refl]

/-- For a quadratic local value and height at least 99/40, the signed correction is nonpositive.
The ramp vanishes and the remaining exponential coefficient is nonnegative. -/
theorem exponentialRampLocalCorrection_tail_nonpos {c : ℂ} (hc : c = 0 ∨ c = 1 ∨ c = -1) {u : ℝ}
    (hu : 99 / 40 ≤ u) (k : ℕ) : exponentialRampLocalCorrection c u k ≤ 0 := by
  have h := mul_nonneg (quadratic_one_add_pow_re_nonneg hc k) (Real.exp_pos (-u)).le
  rw [exponentialRampLocalCorrection, exponentialRampWeight_eq_zero hu]
  linarith only [h]

/-- Twice the number of odd powers through m equals m plus its odd-parity remainder.
Induct using the alternating parity of successive powers; this retains only one endpoint loss. -/
theorem odd_power_double_count (m : ℕ) :
    (∑ k ∈ Finset.range m, if Odd (k + 1) then (2 : ℝ) else 0) =
      (m : ℝ) + if Odd m then 1 else 0 := by
  induction m with
  | zero =>
    norm_num only [Finset.sum_range_zero, Nat.cast_zero, Nat.not_odd_zero, ite_false, zero_add]
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, Nat.cast_add, Nat.cast_one]
    by_cases hm : Odd m
    · have hn : ¬Odd (m + 1) := fun hn ↦ (Nat.odd_add_one.mp hn) hm
      simp only [ite_eq_left hm, ite_eq_right hn, add_zero]
    · have hn : Odd (m + 1) := Nat.odd_add_one.mpr hm
      simp only [ite_eq_right hm, ite_eq_left hn]
      ring

/-- For quadratic local value and nonnegative heights, the first m positive powers
have signed correction sum at most m plus one if the local value is minus one.
Combine the local classifications with exact odd-power counting.
This is the finite per-prime input to conductor-deficit absorption. -/
theorem exponentialRampLocalCorrection_sum_le {c : ℂ} (hc : c = 0 ∨ c = 1 ∨ c = -1) (u : ℕ → ℝ)
    (hu : ∀ k, 0 ≤ u k) (m : ℕ) :
    (∑ k ∈ Finset.range m, exponentialRampLocalCorrection c (u k) (k + 1)) ≤
      (m : ℝ) + if c = -1 then 1 else 0 := by
  rcases hc with rfl | rfl | rfl
  · have hs :=
      Finset.sum_le_sum (s := Finset.range m)
        (fun k _ ↦ exponentialRampLocalCorrection_zero (hu k) (Nat.zero_lt_succ k))
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hs
    have hc0 : (0 : ℂ) ≠ -1 := by norm_num only
    rw [ite_eq_right hc0, add_zero]
    exact hs
  · have hs :=
      Finset.sum_le_sum (s := Finset.range m)
        (fun k _ ↦ exponentialRampLocalCorrection_one (u k) (k + 1))
    simp only [Finset.sum_const_zero] at hs
    have hc1 : (1 : ℂ) ≠ -1 := by norm_num only
    rw [ite_eq_right hc1, add_zero]
    exact hs.trans (Nat.cast_nonneg m)
  · have hs :
      (∑ k ∈ Finset.range m, exponentialRampLocalCorrection (-1) (u k) (k + 1)) ≤
        ∑ k ∈ Finset.range m, if Odd (k + 1) then (2 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro k _
      by_cases hk : Odd (k + 1)
      · rw [ite_eq_left hk]
        exact exponentialRampLocalCorrection_neg_one_odd (hu k) hk
      · rw [ite_eq_right hk]
        exact exponentialRampLocalCorrection_neg_one_even (u k) (Nat.not_odd_iff_even.mp hk)
    rw [odd_power_double_count] at hs
    rw [ite_eq_left (show (-1 : ℂ) = -1 from rfl)]
    by_cases hm : Odd m
    · rw [ite_eq_left hm] at hs
      exact hs
    · rw [ite_eq_right hm, add_zero] at hs
      linarith only [hs]

end PseudoPrime.Analysis
