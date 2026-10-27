/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaRefinedScale

/-! # Interval bounds for the actual ramified dyadic series -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- On a positive scale interval, the actual signed ramified series is
bounded by a finite exponential prefix evaluated at the upper scale and
divided by the lower scale's square root. The signed cutoff tail is dropped
before bounding the prefix. This supplies a sound interval certificate
for the dyadic budget while retaining its actual exponential terms. -/
theorem gamma_ramified_series_le_interval_exp_prefix {p : ℕ} (hp : 1 < p) {x lo hi : ℝ}
    (hlo : 0 < lo) (hlox : lo ≤ x) (hxhi : x ≤ hi) :
    (∑' k : ℕ, exponentialRampLocalCorrection 0 ((p : ℝ) ^ (k + 1) / x) (k + 1)) / Real.sqrt x ≤
      (∑ k ∈ Finset.range ⌊Real.log ((99 / 40 : ℝ) * hi) / Real.log p⌋₊,
          Real.exp (-((p : ℝ) ^ (k + 1) / hi))) /
        Real.sqrt lo := by
  have hx : 0 < x := hlo.trans_le hlox
  have hhi : 0 < hi := hx.trans_le hxhi
  let m := ⌊Real.log ((99 / 40 : ℝ) * hi) / Real.log p⌋₊
  let u := fun k : ℕ ↦ (p : ℝ) ^ (k + 1) / x
  have hdiv (k : ℕ) : (p : ℝ) ^ (k + 1) / hi ≤ u k :=
    div_le_div₀ (pow_nonneg (Nat.cast_nonneg p) _) le_rfl hx hxhi
  have ht : ∀ k, 99 / 40 ≤ u (k + m) := fun k ↦
    (prime_power_tail_above_cutoff hp hhi (Nat.le_add_left m k)).trans (hdiv _)
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

/-- At prime two, combine the actual finite ramified Euler loss with the
full signed ramp series on a scale interval. The Euler cost remains its
exact signed expression and the ramp becomes a finite exponential sum.
This is the quantity whose rational interval certificates must establish
the three-quarters dyadic budget. -/
theorem gamma_dyadic_ramified_actual_cost_le_interval (K : Finset ℕ) {x lo hi : ℝ} (hlo : 0 < lo)
    (hlox : lo ≤ x) (hxhi : x ≤ hi) :
    (∑ k ∈ K, gammaResolventMangoldtWeight (2 ^ (k + 1))) +
        Real.log 2 *
          ((∑' k : ℕ, exponentialRampLocalCorrection 0 ((2 : ℝ) ^ (k + 1) / x) (k + 1)) /
            Real.sqrt x) ≤
      Real.log 2 * gammaPrimeEulerCost 2 +
        Real.log 2 *
          ((∑ k ∈ Finset.range ⌊Real.log ((99 / 40 : ℝ) * hi) / Real.log 2⌋₊,
              Real.exp (-((2 : ℝ) ^ (k + 1) / hi))) /
            Real.sqrt lo) := by
  exact
    add_le_add (sum_gammaResolventMangoldtWeight_primePowers_le_cost Nat.prime_two K)
      (mul_le_mul_of_nonneg_left
        (gamma_ramified_series_le_interval_exp_prefix (by norm_num only) hlo hlox hxhi)
        (Real.log_nonneg (by norm_num only : (1 : ℝ) ≤ 2)))

end PseudoPrime.Analysis
