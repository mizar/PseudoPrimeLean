/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCenteredEndpoint
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterGammaFirstRange

/-! # Centered endpoint with the first Gamma-pole gain -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- An endpoint certificate with the fixed correction `57/500` transfers
to the interval. The proof reuses the monotone residual estimate by shifting
the lower Euler prefix algebraically. -/
theorem quarter_centered_gap_first {a b r L Q s t P : ℝ} (ha : 34 ≤ a) (har : a ≤ r) (hrb : r ≤ b)
    (hlog : Real.log (a ^ 2) ≤ L) (hpow : (a ^ 2) ^ (-(27 / 25 : ℝ)) ≤ Q) (hs : 0 < s)
    (hsqrt : s ≤ Real.sqrt a) (ht : Real.sqrt b ≤ t)
    (hcert :
      quarterCenteredEndpoint a L Q s - 4 * (P - (223 / 125 : ℝ) * (27 / 25 : ℝ) ^ 5) - 57 / 500 ≤
        (27 / 25 : ℝ) ^ 5 * (24439 / 50000 : ℝ) * b - (3 / 4 : ℝ) * b -
          (27 / 25 : ℝ) ^ 5 * (108 / 1000 : ℝ) * t) :
    quarterCenteredResidual r - 4 * (P - (223 / 125 : ℝ) * (27 / 25 : ℝ) ^ 5) - 57 / 500 ≤
      (27 / 25 : ℝ) ^ 5 * (24439 / 50000 : ℝ) * r - (3 / 4 : ℝ) * r -
        (27 / 25 : ℝ) ^ 5 * (108 / 1000 : ℝ) * Real.sqrt r := by
  have hc :
    quarterCenteredEndpoint a L Q s - 4 * ((P + 57 / 2000) - (223 / 125 : ℝ) * (27 / 25 : ℝ) ^ 5) ≤
      (27 / 25 : ℝ) ^ 5 * (24439 / 50000 : ℝ) * b - (3 / 4 : ℝ) * b -
        (27 / 25 : ℝ) ^ 5 * (108 / 1000 : ℝ) * t := by
    linarith only [hcert]
  have h := quarter_centered_gap_of_prefix (P := P + 57 / 2000) ha har hrb hlog hpow hs hsqrt ht hc
  linarith only [h]

end PseudoPrime.PrimeTestBounds.MillerRabin
