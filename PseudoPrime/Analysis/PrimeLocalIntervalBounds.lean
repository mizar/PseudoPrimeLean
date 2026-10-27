/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaDyadicRamifiedBudget

/-! # Generic prime-local rational interval bounds -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- At a base above one and positive scale interval, a cutoff after m powers
bounds the full signed zero-valued ramp series by the first m exponentials at
the upper endpoint, normalized at the lower endpoint. Retain the nonpositive
cutoff tail and compare each prefix term by monotonicity. -/
theorem prime_ramified_series_le_exp_prefix {p : ℕ} (hp : 1 < p) {x lo hi : ℝ} (hlo : 0 < lo)
    (hlox : lo ≤ x) (hxhi : x ≤ hi) (m : ℕ) (hcut : (99 / 40 : ℝ) * hi ≤ (p : ℝ) ^ (m + 1)) :
    (∑' k : ℕ, exponentialRampLocalCorrection 0 ((p : ℝ) ^ (k + 1) / x) (k + 1)) / Real.sqrt x ≤
      (∑ k ∈ Finset.range m, Real.exp (-((p : ℝ) ^ (k + 1) / hi))) / Real.sqrt lo := by
  have hx : 0 < x := hlo.trans_le hlox
  let u := fun k : ℕ ↦ (p : ℝ) ^ (k + 1) / x
  have hdiv (k : ℕ) : (p : ℝ) ^ (k + 1) / hi ≤ u k :=
    div_le_div₀ (pow_nonneg (Nat.cast_nonneg p) _) le_rfl hx hxhi
  have ht : ∀ k, 99 / 40 ≤ u (k + m) := by
    intro k
    apply (le_div_iff₀ hx).mpr
    have hpow : (p : ℝ) ^ (m + 1) ≤ (p : ℝ) ^ (k + m + 1) := by
      exact_mod_cast
        Nat.pow_le_pow_right (Nat.zero_lt_of_lt hp) (Nat.add_le_add_right (Nat.le_add_left m k) 1)
    exact ((mul_le_mul_of_nonneg_left hxhi (by norm_num only)).trans hcut).trans hpow
  have hs :=
    exponentialRampLocalCorrection_tsum_le_prefix (Or.inl rfl) hx u
      (prime_power_div_scale_ge_linear hp hx) m ht
  have hb :=
    Finset.sum_le_sum (s := Finset.range m)
      (fun k hk ↦
        (exponentialRampLocalCorrection_zero_le_weight _ (Nat.succ_pos k)).trans
          (((exponentialRampWeight_bounds _).2).trans (Real.exp_le_exp.mpr (neg_le_neg (hdiv k)))))
  have hn : 0 ≤ ∑ k ∈ Finset.range m, Real.exp (-((p : ℝ) ^ (k + 1) / hi)) :=
    Finset.sum_nonneg (fun k hk ↦ (Real.exp_pos _).le)
  exact
    (div_le_div_of_nonneg_right (hs.trans hb) (Real.sqrt_nonneg x)).trans
      (div_le_div₀ hn le_rfl (Real.sqrt_pos.mpr hlo) (Real.sqrt_le_sqrt hlox))

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
