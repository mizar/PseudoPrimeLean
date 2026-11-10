/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCenteredFirstEndpoint
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterGammaLog183
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterGammaPower183

/-! # Narrow-window centered interval through radius 187.4 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The centered residual fits on radii 183 through 187.4 after retaining the
first Gamma pole, the reflected prefix and the narrow centered-window gain.
The existing independent endpoint certificates control logarithm and power. -/
theorem quarter_centered_narrow_183_1874 {r : ℝ} (hlo : 183 ≤ r) (hhi : r ≤ 937 / 5) :
    quarterCenteredResidual r - 4 * ((291 / 100 : ℝ) - (223 / 125 : ℝ) * (27 / 25 : ℝ) ^ 5) -
        57 / 500 -
        7 / 250 -
        (27 / 25 : ℝ) ^ 5 * (33 / 500) ≤
      (27 / 25 : ℝ) ^ 5 * (24439 / 50000 : ℝ) * r - (3 / 4 : ℝ) * r -
        (27 / 25 : ℝ) ^ 5 * (108 / 1000 : ℝ) * Real.sqrt r := by
  have hs : (13527 / 1000 : ℝ) ≤ Real.sqrt 183 := Real.le_sqrt_of_sq_le (by norm_num only)
  have ht : Real.sqrt (937 / 5) ≤ (13690 / 1000 : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by norm_num only, by norm_num only⟩
  have h :=
    quarter_centered_gap_first (a := 183) (b := 937 / 5) (L := 10419 / 1000) (Q :=
      12975 / 1000000000) (s := 13527 / 1000) (t := 13690 / 1000) (P :=
      291 / 100 + 7 / 1000 + (33 / 2000) * (27 / 25 : ℝ) ^ 5) (by norm_num only) hlo hhi
      quarter_gamma_log183 quarter_gamma_power183 (by norm_num only) hs ht
      (by norm_num only [quarterCenteredEndpoint, quarterMomentPolynomial])
  linarith only [h]

end PseudoPrime.PrimeTestBounds.MillerRabin
