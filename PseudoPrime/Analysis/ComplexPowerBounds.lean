/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Power comparisons in the complex unit disk

Norm and real-part estimates for powers and nonnegative weighted sums are independent
of Dirichlet characters. They support arithmetic comparisons after character evaluation.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For a complex number of norm at most one, its kth power is at distance at most
`k * norm (z-1)` from one. Induct using the triangle inequality; this supplies power deviations. -/
theorem norm_pow_sub_one_le {z : ℂ} (hz : ‖z‖ ≤ 1) (k : ℕ) : ‖z ^ k - 1‖ ≤ (k : ℝ) * ‖z - 1‖ := by
  induction k with
  | zero => simp only [pow_zero, sub_self, norm_zero, Nat.cast_zero, zero_mul, le_refl]
  | succ k
    ih =>
    have he : z ^ (k + 1) - 1 = z * (z ^ k - 1) + (z - 1) := by
      rw [pow_succ]
      ring
    rw [he]
    calc
      _ ≤ ‖z * (z ^ k - 1)‖ + ‖z - 1‖ := norm_add_le _ _
      _ ≤ ‖z ^ k - 1‖ + ‖z - 1‖ := by
        rw [norm_mul]
        exact add_le_add (mul_le_of_le_one_left (norm_nonneg (z ^ k - 1)) hz) (le_refl _)
      _ ≤ (k : ℝ) * ‖z - 1‖ + ‖z - 1‖ := add_le_add ih (le_refl _)
      _ = _ := by
        rw [Nat.cast_add, Nat.cast_one]; ring

/-- For a unit-norm complex number, the squared distance from one equals twice its real
part's deficit. Expand the norm square. This converts norm bounds to cosine-type bounds. -/
theorem norm_sub_one_sq_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) : ‖z - 1‖ ^ 2 = 2 * (1 - z.re) := by
  rw [Complex.sq_norm, Complex.normSq_sub, ← Complex.sq_norm, hz]
  simp only [map_one, mul_one]
  ring

/-- For unit-norm `z`, the real deficit of `z^k` is at most `k²` times that of `z`.
Square the power-distance bound and use the norm-square identity. This is the inequality
used in the paper's proof of Lemma 5.1, without introducing an angular parameter. -/
theorem one_sub_re_pow_le_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) (k : ℕ) :
    1 - (z ^ k).re ≤ (k : ℝ) ^ 2 * (1 - z.re) := by
  have hp : ‖z ^ k‖ = 1 := by rw [norm_pow, hz, one_pow]
  have hn := norm_pow_sub_one_le hz.le k
  have hs : ‖z ^ k - 1‖ ^ 2 ≤ ((k : ℝ) * ‖z - 1‖) ^ 2 := by
    simpa only [pow_two] using mul_self_le_mul_self (norm_nonneg (z ^ k - 1)) hn
  rw [mul_pow, norm_sub_one_sq_of_norm_eq_one hp, norm_sub_one_sq_of_norm_eq_one hz] at hs
  nlinarith only [hs]

/-- For even `k` and unit-norm `z`, the deficit of `Re(z^k)` is bounded by
`k²(1+Re z)`. Apply the general power bound to `-z`. This bounds even prime-power losses. -/
theorem even_power_difference_le {z : ℂ} (hz : ‖z‖ = 1) {k : ℕ} (hk : Even k) :
    1 - (z ^ k).re ≤ (k : ℝ) ^ 2 * (1 + z.re) := by
  have hn : ‖-z‖ = 1 := by rw [norm_neg, hz]
  have h := one_sub_re_pow_le_of_norm_eq_one hn k
  simpa only [neg_pow, hk.neg_one_pow, one_mul, Complex.neg_re, sub_neg_eq_add] using h

/-- For an odd exponent and `norm z ≤ 1`, the real part of `z^k` is at least the
alternating value `-1`. Use the norm bound. Odd powers therefore make a nonnegative contribution. -/
theorem odd_power_difference_nonneg {z : ℂ} (hz : ‖z‖ ≤ 1) {k : ℕ} (hk : Odd k) :
    0 ≤ (z ^ k).re - (-1 : ℝ) ^ k := by
  have hn : ‖z ^ k‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) hz
  have hr := Complex.abs_re_le_norm (z ^ k)
  rw [hk.neg_one_pow]
  exact sub_nonneg.mpr (le_trans (neg_le_of_abs_le (hr.trans hn)) (le_refl _))

/-- For nonnegative weights on a finite exponent set and unit-norm `z`, bound the
alternating comparison difference below by `(1+Re z)` times the sum of the first weight
and the negative even quadratic weights. Sum the odd and even pointwise bounds to obtain
the generic comparison. -/
theorem weighted_power_difference_le {z : ℂ} (hz : ‖z‖ = 1) (s : Finset ℕ) (w : ℕ → ℝ)
    (hw : ∀ k ∈ s, 0 ≤ w k) :
    (1 + z.re) * (∑ k ∈ s, if k = 1 then w k else if Even k then -(k : ℝ) ^ 2 * w k else 0) ≤
      ∑ k ∈ s, w k * ((z ^ k).re - (-1 : ℝ) ^ k) := by
  classical
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  by_cases h1 : k = 1
  · subst k
    simp only [ite_true, pow_one]
    ring_nf
    exact le_refl _
  · rw [ite_eq_right h1]
    rcases Nat.even_or_odd k with he | ho
    · rw [ite_eq_left he, he.neg_one_pow]
      have h := mul_le_mul_of_nonneg_left (even_power_difference_le hz he) (hw k hk)
      nlinarith only [h]
    · rw [ite_eq_right (Nat.not_even_iff_odd.mpr ho), mul_zero]
      exact mul_nonneg (hw k hk) (odd_power_difference_nonneg hz.le ho)

/-- A unit-norm complex number satisfies `z² = 2 Re(z) z - 1`.
Expand real and imaginary parts and use the norm-square condition. This yields the
real-power recurrence used for the exceptional prime-two polynomial. -/
theorem sq_eq_two_re_mul_sub_one_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) :
    z ^ 2 = ((2 * z.re : ℝ) : ℂ) * z - 1 := by
  have hn : z.re * z.re + z.im * z.im = 1 := by
    have h := Complex.sq_norm z
    rw [hz, Complex.normSq_apply] at h
    simpa only [one_pow] using h.symm
  apply Complex.ext
  · simp only [pow_two, Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.one_re, zero_mul, sub_zero]
    nlinarith only [hn]
  · simp only [pow_two, Complex.mul_im, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.one_im, zero_mul, add_zero, sub_zero]
    ring

/-- Real parts of powers of a unit-norm complex number satisfy the second-order
recurrence `Re(z^(k+2)) = 2 Re(z) Re(z^(k+1)) - Re(z^k)`.
Multiply the quadratic identity by `z^k`; this computes the first five comparison terms. -/
theorem re_pow_add_two_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) (k : ℕ) :
    (z ^ (k + 2)).re = 2 * z.re * (z ^ (k + 1)).re - (z ^ k).re := by
  have h : z ^ (k + 2) = ((2 * z.re : ℝ) : ℂ) * z ^ (k + 1) - z ^ k := by
    rw [pow_add, sq_eq_two_re_mul_sub_one_of_norm_eq_one hz, pow_succ]
    ring
  rw [h]
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero]

end PseudoPrime.Analysis
