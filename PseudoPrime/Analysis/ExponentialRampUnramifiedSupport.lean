/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ExponentialRampLocalSeries

/-! # Nonpositive ramp corrections outside the ambient prime support -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For a prime base and positive scale, a quadratic local value which is one
whenever the base is below the ramp cutoff has nonpositive correction at every
positive power. Below the cutoff use the value one; above it retain the signed tail.
This removes primes outside the ambient modulus from the arithmetic comparison. -/
theorem exponentialRamp_unramified_power_nonpos {p : ℕ} (hp : p.Prime) {x : ℝ} (hx : 0 < x) {c : ℂ}
    (hc : c = 0 ∨ c = 1 ∨ c = -1) (hone : (p : ℝ) ≤ (99 / 40 : ℝ) * x → c = 1) (k : ℕ) :
    exponentialRampLocalCorrection c ((p : ℝ) ^ (k + 1) / x) (k + 1) ≤ 0 := by
  by_cases hcut : (p : ℝ) ≤ (99 / 40 : ℝ) * x
  · rw [hone hcut]
    exact exponentialRampLocalCorrection_one _ _
  · have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
    have hpow := le_self_pow₀ hpR (Nat.succ_ne_zero k)
    exact
      exponentialRampLocalCorrection_tail_nonpos hc
        ((le_div_iff₀ hx).mpr ((not_le.mp hcut).le.trans hpow)) _

/-- Under the same local hypotheses, the full positive-power correction series
converges and has nonpositive sum. Use the exponential geometric majorant and
the pointwise signed estimate. This permits omitting these primes after reindexing. -/
theorem exponentialRamp_unramified_series_nonpos {p : ℕ} (hp : p.Prime) {x : ℝ} (hx : 0 < x) {c : ℂ}
    (hc : c = 0 ∨ c = 1 ∨ c = -1) (hone : (p : ℝ) ≤ (99 / 40 : ℝ) * x → c = 1) :
    Summable (fun k : ℕ ↦ exponentialRampLocalCorrection c ((p : ℝ) ^ (k + 1) / x) (k + 1)) ∧
      (∑' k : ℕ, exponentialRampLocalCorrection c ((p : ℝ) ^ (k + 1) / x) (k + 1)) ≤ 0 := by
  constructor
  · exact
      summable_exponentialRampLocalCorrection hc hx _ (prime_power_div_scale_ge_linear hp.one_lt hx)
  · exact tsum_nonpos (exponentialRamp_unramified_power_nonpos hp hx hc hone)

end PseudoPrime.Analysis
