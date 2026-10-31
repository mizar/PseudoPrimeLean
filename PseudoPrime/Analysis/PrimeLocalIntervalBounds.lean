/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.PrimeLocalCertificates

public import PseudoPrime.Analysis.GammaRampPrimeCosts

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

end PseudoPrime.Analysis
