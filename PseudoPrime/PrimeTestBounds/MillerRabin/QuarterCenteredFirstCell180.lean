/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCenteredFirstEndpoint
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterGammaLog180
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterGammaPower180

/-! # First corrected centered interval -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- On radii `180` through `183`, the centered residual fits after retaining
the three first-pole corrections and using the Euler prefix `291/100`. The
logarithm and negative power are independently certified at the endpoint. -/
theorem quarter_centered_first_180_183 {r : ℝ} (hlo : 180 ≤ r) (hhi : r ≤ 183) :
    quarterCenteredResidual r - 4 * ((291 / 100 : ℝ) - (223 / 125 : ℝ) * (27 / 25 : ℝ) ^ 5) -
        57 / 500 ≤
      (27 / 25 : ℝ) ^ 5 * (24439 / 50000 : ℝ) * r - (3 / 4 : ℝ) * r -
        (27 / 25 : ℝ) ^ 5 * (108 / 1000 : ℝ) * Real.sqrt r := by
  have hs : (13416 / 1000 : ℝ) ≤ Real.sqrt 180 := Real.le_sqrt_of_sq_le (by norm_num only)
  have ht : Real.sqrt 183 ≤ (13528 / 1000 : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by norm_num only, by norm_num only⟩
  apply
    quarter_centered_gap_first (a := 180) (b := 183) (L := 5193 / 500) (Q := 269 / 20000000) (s :=
      13416 / 1000) (t := 13528 / 1000) (P := 291 / 100) (by norm_num only) hlo hhi
      quarter_gamma_log180 quarter_gamma_power180 (by norm_num only) hs ht
  norm_num only [quarterCenteredEndpoint, quarterMomentPolynomial]

end PseudoPrime.PrimeTestBounds.MillerRabin
