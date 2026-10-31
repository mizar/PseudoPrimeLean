/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaExpRationalBounds
public import PseudoPrime.Analysis.GeometricRatioBounds

/-! # Rational prime-power and signed geometric certificates -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The rational reciprocal-Taylor upper sum for m positive powers of a natural
base at a rational upper scale. It supplies compact finite local interval certificates. -/
def primeExpPrefixUpper (p : ℕ) (b : ℚ) (m : ℕ) : ℚ :=
  ∑ k ∈ Finset.range m, gammaExpTaylorUpper ((p : ℚ) ^ (k + 1) / b)

/-- At a positive rational scale, the rational exponential prefix bounds the
actual finite exponential sum. Apply the proved reciprocal-Taylor estimate
termwise and cast powers and finite sums into the reals. -/
theorem prime_exp_prefix_upper_valid (p : ℕ) {b : ℚ} (hb : 0 < b) (m : ℕ) :
    (∑ k ∈ Finset.range m, Real.exp (-((p : ℝ) ^ (k + 1) / (b : ℝ)))) ≤
      (primeExpPrefixUpper p b m : ℝ) := by
  simp only [primeExpPrefixUpper, Rat.cast_sum]
  apply Finset.sum_le_sum
  intro k hk
  have h :=
    gamma_exp_taylor_upper_valid
      (div_nonneg (pow_nonneg (Nat.cast_nonneg p : (0 : ℚ) ≤ p) (k + 1)) hb.le)
  simpa only [Rat.cast_div, Rat.cast_pow, Rat.cast_natCast] using h

/-- The sign-sensitive rational geometric upper allowance from ratio endpoints.
Use the upper endpoint for nonnegative coefficients and the lower for negative
coefficients, preserving cancellation before summing different nodes. -/
def rationalGeometricUpper (c lo hi : ℚ) (j : ℕ) : ℚ :=
  let r := if 0 ≤ c then hi else lo
  c * (r / (1 - r ^ j))

/-- A signed real geometric node is bounded by its rational allowance when the
ratio lies in a nonnegative interval below one. Monotonicity and coefficient
sign select the correct endpoint for any positive natural progression step. -/
theorem signed_geometric_node_le_interval {r : ℝ} {c lo hi : ℚ} (hl0 : 0 ≤ lo) (hlo : (lo : ℝ) ≤ r)
    (hhi : r ≤ (hi : ℝ)) (hu : hi < 1) {j : ℕ} (hj : 0 < j) :
    (c : ℝ) * (r / (1 - r ^ j)) ≤ (rationalGeometricUpper c lo hi j : ℝ) := by
  have hlR := (Rat.cast_le (K := ℝ)).mpr hl0
  have huR := (Rat.cast_lt (K := ℝ)).mpr hu
  norm_num only [Rat.cast_zero, Rat.cast_one] at hlR huR
  by_cases hc : 0 ≤ c
  · simp only [rationalGeometricUpper, ite_eq_left hc, Rat.cast_mul, Rat.cast_div, Rat.cast_sub,
      Rat.cast_one, Rat.cast_pow]
    exact
      mul_le_mul_of_nonneg_left (gamma_geometric_ratio_monotone (hlR.trans hlo) hhi huR hj)
        (by exact_mod_cast hc)
  · simp only [rationalGeometricUpper, ite_eq_right hc, Rat.cast_mul, Rat.cast_div, Rat.cast_sub,
      Rat.cast_one, Rat.cast_pow]
    exact
      mul_le_mul_of_nonpos_left (gamma_geometric_ratio_monotone hlR hlo (hhi.trans_lt huR) hj)
        (by exact_mod_cast le_of_not_ge hc)

end PseudoPrime.Analysis
