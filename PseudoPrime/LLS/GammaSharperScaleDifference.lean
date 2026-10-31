/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.PrimeExponentialMomentRefinements

public import PseudoPrime.LLS.GammaExponentialScaleDifference

/-! # Analytic improvement of the prime-power scale modulus from 9/2 to 3 -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: p>=3 and positive ordered endpoints a<=b with b>=1.
Claim: lowering the left endpoint increases the numerator by at most 3(b-a)/a.
Use the mass difference. Role: transport existing signed numerator bounds. -/
theorem gamma_window_numerator_le_lowered_left_three {p : ℕ} (hp : 3 ≤ p) {a b hi θ : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : 1 ≤ b) :
    gammaRamifiedWindowNumerator p a hi θ ≤
      gammaRamifiedWindowNumerator p b hi θ + (3 : ℝ) * (b - a) / a := by
  have h := Analysis.gamma_prime_exponential_mass_difference_le_three hp ha hab hb
  dsimp only [gammaRamifiedWindowNumerator]
  linarith only [h]

/-- Input: an envelope-checked prime row with p>=3 and a new positive left
endpoint below the old one. Claim: its stored ramp cap plus the common
scale correction bounds the new numerator. Role: reuse numerical row data. -/
theorem GammaLocalPrimeRow.window_numerator_le_lowered_left_three (r : GammaLocalPrimeRow)
    (c : GammaLocalCellData) (hcell : c.check = true) (hp : r.prime.Prime) (h3 : 3 ≤ r.prime)
    (hc : r.envelopeCheck c = true) {a : ℝ} (ha : 0 < a) (hab : a ≤ (c.lo : ℝ))
    (hb : (1 : ℝ) ≤ c.lo) (θ : ℝ) :
    gammaRamifiedWindowNumerator r.prime a c.hi θ ≤
      (r.rampUpper : ℝ) - θ + (3 : ℝ) * ((c.lo : ℝ) - a) / a := by
  have hs := gamma_window_numerator_le_lowered_left_three h3 ha hab hb (hi := c.hi) (θ := θ)
  have hr := r.window_numerator_le_of_envelope c hcell hp hc θ
  linarith only [hs, hr]

end PseudoPrime.LLS

namespace PseudoPrime.LLS

/-- Input: a checked cell, an envelope-checked prime row and a lower positive
left endpoint. Claim: the old ramp cap with its base-sensitive correction bounds
the new numerator. Use the analytic mass difference and existing row bound.
Role: lower a window without generating new prime-specific data. -/
theorem GammaLocalPrimeRow.window_numerator_le_lowered_left_base_ratio (r : GammaLocalPrimeRow)
    (c : GammaLocalCellData) (hcell : c.check = true) (hp : r.prime.Prime)
    (hc : r.envelopeCheck c = true) {a : ℝ} (ha : 0 < a) (hab : a ≤ (c.lo : ℝ))
    (hb : (1 : ℝ) ≤ c.lo) (θ : ℝ) :
    gammaRamifiedWindowNumerator r.prime a c.hi θ ≤
      (r.rampUpper : ℝ) - θ + (((r.prime : ℝ) + 1) / (r.prime - 1)) * ((c.lo : ℝ) - a) / a := by
  have hs := Analysis.gamma_prime_exponential_mass_difference_le_base_ratio hp.one_lt ha hab hb
  have hr := r.window_numerator_le_of_envelope c hcell hp hc θ
  dsimp only [gammaRamifiedWindowNumerator] at hs hr ⊢
  linarith only [hs, hr]

end PseudoPrime.LLS
