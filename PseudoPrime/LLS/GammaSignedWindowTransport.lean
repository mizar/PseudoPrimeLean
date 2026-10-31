/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.SignedSqrtBounds

public import PseudoPrime.Analysis.ExponentialSeriesBounds

public import PseudoPrime.LLS.GammaSignedRampCellBounds
public import PseudoPrime.LLS.GammaActualRamifiedBudget
public import PseudoPrime.LLS.GammaAnchoredRamifiedSupport

/-! # Signed endpoint transport of full local ramp series -/

@[expose] public section

namespace PseudoPrime.LLS
end PseudoPrime.LLS

namespace PseudoPrime.LLS

/-- Input: natural base p and scale x. Definition: the complete signed local
ramp series at character value zero. Role: keep the exact signed quantity
in scale transport; summability is supplied at positive admissible scales. -/
noncomputable def gammaRamifiedRampMass (p : ℕ) (x : ℝ) : ℝ :=
  ∑' k : ℕ, Analysis.exponentialRampLocalCorrection 0 ((p : ℝ) ^ (k + 1) / x) (k + 1)

/-- Input: p>1 and 0<lo<=x<=hi. Claim: the signed mass at x is at most the
mass at hi plus the difference of endpoint exponential masses. Use ramp and
exponential monotonicity, then sum convergent series. Role: retain tail signs. -/
theorem gamma_ramified_ramp_mass_le_window {p : ℕ} (hp : 1 < p) {lo x hi : ℝ} (hlo : 0 < lo)
    (hlox : lo ≤ x) (hxhi : x ≤ hi) :
    gammaRamifiedRampMass p x ≤
      gammaRamifiedRampMass p hi + Analysis.gammaPrimeExponentialMass p hi -
        Analysis.gammaPrimeExponentialMass p lo := by
  have hx := hlo.trans_le hlox
  have hhi := hx.trans_le hxhi
  have hsx :=
    Analysis.summable_exponentialRampLocalCorrection (c := (0 : ℂ)) (Or.inl rfl) hx _
      (Analysis.prime_power_div_scale_ge_linear hp hx)
  have hsh :=
    Analysis.summable_exponentialRampLocalCorrection (c := (0 : ℂ)) (Or.inl rfl) hhi _
      (Analysis.prime_power_div_scale_ge_linear hp hhi)
  have heh :=
    Analysis.summable_exp_neg_of_linear_lower hhi _
      (Analysis.prime_power_div_scale_ge_linear hp hhi)
  have hel :=
    Analysis.summable_exp_neg_of_linear_lower hlo _
      (Analysis.prime_power_div_scale_ge_linear hp hlo)
  have h :=
    hsx.tsum_le_tsum
      (fun k ↦
        show
          Analysis.exponentialRampLocalCorrection 0 ((p : ℝ) ^ (k + 1) / x) (k + 1) ≤
            Analysis.exponentialRampLocalCorrection 0 ((p : ℝ) ^ (k + 1) / hi) (k + 1) +
                Real.exp (-((p : ℝ) ^ (k + 1) / hi)) -
              Real.exp (-((p : ℝ) ^ (k + 1) / lo))
          from by
          have ht :=
            gamma_ramified_local_term_le_signed_cell (pow_nonneg (Nat.cast_nonneg p) (k + 1)) hlo
              hlox hxhi (Nat.succ_pos k)
          simpa only [Analysis.exponentialRampLocalCorrection, zero_pow (Nat.succ_ne_zero k),
            add_zero, Complex.one_re, one_mul, sub_add_cancel] using ht)
      ((hsh.add heh).sub hel)
  rw [(hsh.add heh).tsum_sub hel, hsh.tsum_add heh] at h
  exact h

end PseudoPrime.LLS

namespace PseudoPrime.LLS

/-- Input: base p, endpoints lo/hi and dual parameter theta. Definition:
the signed endpoint mass bound minus theta. Role: provide a common numerator
for the normalized local dual cost throughout an interval. -/
noncomputable def gammaRamifiedWindowNumerator (p : ℕ) (lo hi θ : ℝ) : ℝ :=
  gammaRamifiedRampMass p hi + Analysis.gammaPrimeExponentialMass p hi -
    Analysis.gammaPrimeExponentialMass p lo -
    θ

/-- Input: p>1 and a positive scale window. Claim: Euler cost plus the larger
endpoint quotient bounds the signed cost minus theta/sqrt(x). Combine signed
mass transport and the denominator bound. Role: preserve local cancellation. -/
theorem gamma_ramified_signed_cost_sub_theta_le_window {p : ℕ} (hp : 1 < p) {lo x hi θ : ℝ}
    (hlo : 0 < lo) (hlox : lo ≤ x) (hxhi : x ≤ hi) :
    gammaRamifiedSignedCombinedCost p x - gammaRamifiedThetaParameter θ x ≤
      Analysis.gammaPrimeEulerCost p +
        max (gammaRamifiedWindowNumerator p lo hi θ / Real.sqrt lo)
          (gammaRamifiedWindowNumerator p lo hi θ / Real.sqrt hi) := by
  have hm := gamma_ramified_ramp_mass_le_window hp hlo hlox hxhi
  have hn : gammaRamifiedRampMass p x - θ ≤ gammaRamifiedWindowNumerator p lo hi θ := by
    dsimp only [gammaRamifiedWindowNumerator]
    linarith only [hm]
  have hdiv :=
    (div_le_div_of_nonneg_right hn (Real.sqrt_nonneg x)).trans
      (Analysis.signed_div_le_max_endpoints hlo hlox hxhi)
  change
    Analysis.gammaPrimeEulerCost p + gammaRamifiedRampMass p x / Real.sqrt x - θ / Real.sqrt x ≤ _
  rw [add_sub_assoc, ← sub_div]
  exact add_le_add le_rfl hdiv

end PseudoPrime.LLS

namespace PseudoPrime.LLS

/-- Input: window endpoints, Euler cap e and numerator cap N. Definition:
the nonnegative part of e plus the maximum of endpoint quotients of N.
Role: produce one interval-wide local excess allowance. -/
noncomputable def gammaRamifiedWindowExcessBound (lo hi e N : ℝ) : ℝ :=
  max (e + max (N / Real.sqrt lo) (N / Real.sqrt hi)) 0

/-- Input: a positive scale window and Euler/numerator caps for p>1.
Claim: the positive local dual excess is bounded by the fixed row allowance.
Use the signed cost transport and monotonicity. Role: certify a whole window. -/
theorem gamma_ramified_excess_le_window_row {p : ℕ} (hp : 1 < p) {lo x hi θ e N : ℝ} (hlo : 0 < lo)
    (hlox : lo ≤ x) (hxhi : x ≤ hi) (he : Analysis.gammaPrimeEulerCost p ≤ e)
    (hN : gammaRamifiedWindowNumerator p lo hi θ ≤ N) :
    max (gammaRamifiedSignedCombinedCost p x - gammaRamifiedThetaParameter θ x) 0 ≤
      gammaRamifiedWindowExcessBound lo hi e N := by
  have h := gamma_ramified_signed_cost_sub_theta_le_window (θ := θ) hp hlo hlox hxhi
  have hn :=
    max_le_max (div_le_div_of_nonneg_right hN (Real.sqrt_nonneg lo))
      (div_le_div_of_nonneg_right hN (Real.sqrt_nonneg hi))
  exact max_le_max (h.trans (add_le_add he hn)) le_rfl

/-- Input: a prime set, a positive scale window and per-prime endpoint caps.
Claim: the weighted actual excess is bounded by the fixed row sum.
Multiply by nonnegative log-prime weights and sum. Role: supply dual budgets. -/
theorem gamma_ramified_window_excess_sum_le (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) {lo x hi θ : ℝ}
    (hlo : 0 < lo) (hlox : lo ≤ x) (hxhi : x ≤ hi) (e N : ℕ → ℝ)
    (he : ∀ p ∈ S, Analysis.gammaPrimeEulerCost p ≤ e p)
    (hN : ∀ p ∈ S, gammaRamifiedWindowNumerator p lo hi θ ≤ N p) :
    (∑ p ∈ S,
        Real.log p *
          max (gammaRamifiedSignedCombinedCost p x - gammaRamifiedThetaParameter θ x) 0) ≤
      ∑ p ∈ S, Real.log p * gammaRamifiedWindowExcessBound lo hi (e p) (N p) := by
  apply Finset.sum_le_sum
  intro p hp
  exact
    mul_le_mul_of_nonneg_left
      (gamma_ramified_excess_le_window_row (hS p hp).one_lt hlo hlox hxhi (he p hp) (hN p hp))
      (Real.log_nonneg (by exact_mod_cast (hS p hp).one_le))

end PseudoPrime.LLS

namespace PseudoPrime.LLS

/-- Input: the upper scale endpoint hi. Definition: odd primes in the anchored
support max(160,1+(52/25)sqrt(hi)). Role: fix one support for a whole interval. -/
noncomputable def gammaAnchoredWindowPrimeSet (hi : ℝ) : Finset ℕ :=
  gammaRamifiedCertificatePrimeSet (max 160 (1 + (52 / 25 : ℝ) * Real.sqrt hi))

end PseudoPrime.LLS
