/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.PrimeExponentialMoments

public import PseudoPrime.Analysis.GammaSignedEulerTail
public import PseudoPrime.LLS.GammaWindowRowBounds
public import PseudoPrime.Analysis.GaussianGammaCutoffCurvature

/-! # Analytic scale differences for sparse prime-power exponential masses -/

@[expose] public section

namespace PseudoPrime.LLS
end PseudoPrime.LLS

namespace PseudoPrime.LLS
end PseudoPrime.LLS

namespace PseudoPrime.LLS
end PseudoPrime.LLS

namespace PseudoPrime.LLS
end PseudoPrime.LLS

namespace PseudoPrime.LLS
end PseudoPrime.LLS

namespace PseudoPrime.LLS

/-- Input: p>=3 and positive ordered left endpoints a<=b with b>=1.
Claim: moving the left endpoint to a increases the signed window numerator
by at most (9/2)(b-a)/a. Use the exponential mass difference.
Role: reuse an existing interval certificate on a larger interval. -/
theorem gamma_ramified_window_numerator_le_lowered_left {p : ℕ} (hp : 3 ≤ p) {a b hi θ : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : 1 ≤ b) :
    gammaRamifiedWindowNumerator p a hi θ ≤
      gammaRamifiedWindowNumerator p b hi θ + (9 / 2 : ℝ) * (b - a) / a := by
  have h := Analysis.gamma_prime_exponential_mass_difference_le hp ha hab hb
  dsimp only [gammaRamifiedWindowNumerator]
  linarith only [h]

/-- Input: an envelope-checked prime row with p>=3 and a new positive left
endpoint below the old one. Claim: its stored ramp cap plus the common
scale correction bounds the new numerator. Role: reuse numerical row data. -/
theorem GammaLocalPrimeRow.window_numerator_le_lowered_left (r : GammaLocalPrimeRow)
    (c : GammaLocalCellData) (hcell : c.check = true) (hp : r.prime.Prime) (h3 : 3 ≤ r.prime)
    (hc : r.envelopeCheck c = true) {a : ℝ} (ha : 0 < a) (hab : a ≤ (c.lo : ℝ))
    (hb : (1 : ℝ) ≤ c.lo) (θ : ℝ) :
    gammaRamifiedWindowNumerator r.prime a c.hi θ ≤
      (r.rampUpper : ℝ) - θ + (9 / 2 : ℝ) * ((c.lo : ℝ) - a) / a := by
  have hs := gamma_ramified_window_numerator_le_lowered_left h3 ha hab hb (hi := c.hi) (θ := θ)
  have hr := r.window_numerator_le_of_envelope c hcell hp hc θ
  linarith only [hs, hr]

end PseudoPrime.LLS
