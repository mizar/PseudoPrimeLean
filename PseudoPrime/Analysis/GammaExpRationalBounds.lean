/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaDyadicEulerCertificate

/-! # Rational Taylor upper bounds for the dyadic exponential prefix -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Reciprocal of the positive exponential Taylor sum through degree fifteen.
At a nonnegative rational input it bounds exp(-t), as proved below. This
rational expression supplies finite dyadic interval certificates. -/
def gammaExpTaylorUpper (t : ℚ) : ℚ :=
  (∑ i ∈ Finset.range 16, t ^ i / (i.factorial : ℚ))⁻¹

/-- For a nonnegative real input, exp(-t) is at most the reciprocal of the
Taylor sum through degree fifteen. The positive exponential exceeds every
partial sum and the constant term makes the partial sum positive. Taking
reciprocals gives the upper bound needed for the interval prefix. -/
theorem gamma_exp_neg_le_reciprocal_taylor {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-t) ≤ (∑ i ∈ Finset.range 16, t ^ i / (i.factorial : ℝ))⁻¹ := by
  have hpos : (1 : ℝ) ≤ ∑ i ∈ Finset.range 16, t ^ i / (i.factorial : ℝ) := by
    have h :=
      Finset.single_le_sum (s := Finset.range 16) (f := fun i ↦ t ^ i / (i.factorial : ℝ))
        (fun i hi ↦ div_nonneg (pow_nonneg ht _) (Nat.cast_nonneg _))
        (by norm_num only [Finset.mem_range] : 0 ∈ Finset.range 16)
    simpa only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one] using h
  rw [Real.exp_neg]
  exact
    (inv_le_inv₀ (Real.exp_pos t) (zero_lt_one.trans_le hpos)).mpr (Real.sum_le_exp_of_nonneg ht 16)

/-- At a nonnegative rational input, the rational Taylor expression
bounds the real negative exponential. Cast finite sums, powers and factorials
into the reals and apply the analytic reciprocal Taylor bound. -/
theorem gamma_exp_taylor_upper_valid {t : ℚ} (ht : 0 ≤ t) :
    Real.exp (-(t : ℝ)) ≤ (gammaExpTaylorUpper t : ℝ) := by
  simpa only [gammaExpTaylorUpper, Rat.cast_inv, Rat.cast_sum, Rat.cast_div, Rat.cast_pow,
    Rat.cast_natCast] using gamma_exp_neg_le_reciprocal_taylor (by exact_mod_cast ht : (0 : ℝ) ≤ t)

/-- Rational upper bound for the first m dyadic exponential terms at scale b.
Sum the validated Taylor reciprocal at each rational height 2^(k+1)/b.
This expression is evaluated by exact arithmetic in interval certificates. -/
def gammaDyadicExpPrefixUpper (b : ℚ) (m : ℕ) : ℚ :=
  ∑ k ∈ Finset.range m, gammaExpTaylorUpper ((2 : ℚ) ^ (k + 1) / b)

/-- The rational dyadic prefix bounds its actual real finite exponential sum
at every positive rational scale. Apply the negative-exponential bound to
each term and cast the sum. This connects exact certificate data to the
previously proved actual signed-series interval interface. -/
theorem gamma_dyadic_exp_prefix_upper_valid {b : ℚ} (hb : 0 < b) (m : ℕ) :
    (∑ k ∈ Finset.range m, Real.exp (-((2 : ℝ) ^ (k + 1) / (b : ℝ)))) ≤
      (gammaDyadicExpPrefixUpper b m : ℝ) := by
  simp only [gammaDyadicExpPrefixUpper, Rat.cast_sum]
  apply Finset.sum_le_sum
  intro k hk
  have h :=
    gamma_exp_taylor_upper_valid
      (div_nonneg (pow_nonneg (by norm_num only : (0 : ℚ) ≤ 2) (k + 1)) hb.le)
  simpa only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] using h

end PseudoPrime.Analysis
