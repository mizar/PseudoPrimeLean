/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.RationalPowerBounds
public import PseudoPrime.Analysis.LogTaylorBounds
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.TruncatedMangoldtBounds

/-! # Rational certificates for finite Dirichlet prefixes and Euler bounds -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Check a positive rational input, a nonnegative Taylor displacement below one,
and containment of the rational upper Taylor endpoint. The power-of-two scale
uses the numerator bit length. The output certifies a real logarithm upper bound. -/
def rationalLogUpperCheck (N : ℚ) (terms : ℕ) (hi : ℚ) : Bool :=
  let j := Nat.log2 N.num.natAbs + 1
  let x := 1 - N / 2 ^ j
  decide
    (0 < N ∧
      0 ≤ x ∧
      x < 1 ∧
      (j : ℚ) * (6931471808 / 10000000000) - rationalLogSeries x terms + x ^ (terms + 1) / (1 - x) ≤
        hi)

/-- A successful upper-only logarithm check bounds the real logarithm by hi.
Use nonnegativity to remove the absolute value in the existing Taylor bound.
This supplies a kernel-computable scalar test for Euler-prefix certificates. -/
theorem rationalLogUpperCheck_sound {N hi : ℚ} {terms : ℕ}
    (h : rationalLogUpperCheck N terms hi = true) : Real.log (N : ℝ) ≤ (hi : ℝ) := by
  let j := Nat.log2 N.num.natAbs + 1
  let x := 1 - N / 2 ^ j
  have hc :
    0 < N ∧
      0 ≤ x ∧
      x < 1 ∧
      (j : ℚ) * (6931471808 / 10000000000) - rationalLogSeries x terms + x ^ (terms + 1) / (1 - x) ≤
        hi :=
    of_decide_eq_true h
  have hx : |1 - N / 2 ^ j| < 1 := by
    rw [show 1 - N / 2 ^ j = x from rfl, abs_of_nonneg hc.2.1]
    exact hc.2.2.1
  have hu := (rationalLogBounds_sound hc.1 j terms hx).2
  have he :
    rationalLogUpper N j terms =
      (j : ℚ) * (6931471808 / 10000000000) - rationalLogSeries x terms +
        x ^ (terms + 1) / (1 - x) := by
    simp only [rationalLogUpper, rationalLogRemainder, show 1 - N / 2 ^ j = x from rfl,
      abs_of_nonneg hc.2.1]
  rw [he] at hu
  exact hu.trans ((Rat.cast_le (K := ℝ)).mpr hc.2.2.2)

/-- For r>0, bounds for logarithmic prefix terms and both tail factors bound the
truncated numerator. Split off zero and compare nonnegative products.
This connects finite interval data to the analytic numerator cap. -/
theorem truncatedLogDirichletUpper_le_of_prefix {r : ℝ} (hr : 0 < r) (N : ℕ) (ell u : ℕ → ℝ)
    {ellN tail : ℝ} (hl : ∀ i ∈ Finset.range N, Real.log (i + 1 : ℕ) ≤ ell i)
    (hu : ∀ i ∈ Finset.range N, (i + 1 : ℕ) ^ (-r - 1) ≤ u i) (hN : Real.log N ≤ ellN)
    (ht : (N : ℝ) ^ (-r) ≤ tail) :
    truncatedLogDirichletUpper r N ≤
      (∑ i ∈ Finset.range N, ell i * u i) + tail * (ellN / r + r⁻¹ ^ 2) := by
  have hs :
    (∑ i ∈ Finset.range N, Real.log (i + 1 : ℕ) * (i + 1 : ℕ) ^ (-r - 1)) ≤
      ∑ i ∈ Finset.range N, ell i * u i := by
    refine Finset.sum_le_sum (fun i hi ↦ ?_)
    exact
      mul_le_mul (hl i hi) (hu i hi) (Real.rpow_nonneg (Nat.cast_nonneg (i + 1)) _)
        ((Real.log_natCast_nonneg (i + 1)).trans (hl i hi))
  have hbracket : Real.log N / r + r⁻¹ ^ 2 ≤ ellN / r + r⁻¹ ^ 2 :=
    add_le_add (div_le_div_of_nonneg_right hN hr.le) (le_refl _)
  have htail :=
    mul_le_mul ht hbracket
      (add_nonneg (div_nonneg (Real.log_natCast_nonneg N) hr.le) (sq_nonneg r⁻¹))
      ((Real.rpow_nonneg (Nat.cast_nonneg N) _).trans ht)
  unfold truncatedLogDirichletUpper
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, Real.log_zero, zero_mul, add_zero]
  exact add_le_add hs htail

/-- For r>0, lower prefix endpoints and a tail-power lower endpoint bound the
truncated denominator from below. Split off zero and sum inequalities.
This connects finite interval data to the analytic denominator floor. -/
theorem prefix_le_truncatedPowerDirichletLower {r : ℝ} (hr : 0 < r) (N : ℕ) (lo : ℕ → ℝ) {tail : ℝ}
    (hl : ∀ i ∈ Finset.range N, lo i ≤ (i + 1 : ℕ) ^ (-r - 1))
    (ht : tail ≤ ((N + 1 : ℕ) : ℝ) ^ (-r)) :
    (∑ i ∈ Finset.range N, lo i) + tail / r ≤ truncatedPowerDirichletLower r N := by
  have hs := Finset.sum_le_sum hl
  unfold truncatedPowerDirichletLower
  rw [Finset.sum_range_succ']
  rw [Nat.cast_zero, Real.zero_rpow (by linarith only [hr] : -r - 1 ≠ 0), add_zero]
  exact add_le_add hs (div_le_div_of_nonneg_right ht hr.le)

end PseudoPrime.Analysis
