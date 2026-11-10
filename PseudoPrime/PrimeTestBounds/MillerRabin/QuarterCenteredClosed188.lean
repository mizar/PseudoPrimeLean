/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEulerTail183
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCenteredNarrow1874

/-! Closed-tail residual certificate for radii 183 through 188. -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The sharp closed-tail residual satisfies the centered witness inequality on radii 183 to
188. The Euler-tail cap and the independently certified endpoint bounds control the interval. -/
theorem quarter_closed_residual_183_188 {r : ℝ} (hlo : 183 ≤ r) (hhi : r ≤ 188) :
    quarterCenteredClosedResidual r - 57 / 500 - 7 / 250 - (27 / 25 : ℝ) ^ 5 * (33 / 500) ≤
      (27 / 25 : ℝ) ^ 5 * (24439 / 50000 : ℝ) * r - (3 / 4 : ℝ) * r -
        (27 / 25 : ℝ) ^ 5 * (108 / 1000 : ℝ) * Real.sqrt r := by
  have hs : (13527 / 1000 : ℝ) ≤ Real.sqrt 183 := Real.le_sqrt_of_sq_le (by norm_num only)
  have ht : Real.sqrt 188 ≤ (13712 / 1000 : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by norm_num only, by norm_num only⟩
  have h :=
    quarter_centered_gap_first (a := 183) (b := 188) (L := 10419 / 1000) (Q := 12975 / 1000000000)
      (s := 13527 / 1000) (t := 13712 / 1000) (P :=
      (843 / 400 : ℝ) * (27 / 25 : ℝ) ^ 5 - 63 / 500 + 7 / 1000 +
        (33 / 2000 : ℝ) * (27 / 25 : ℝ) ^ 5)
      (by norm_num only) hlo hhi quarter_gamma_log183 quarter_gamma_power183 (by norm_num only) hs
      ht (by norm_num only [quarterCenteredEndpoint, quarterMomentPolynomial])
  have hc := quarter_euler_tail_183_196 hlo (by linarith only [hhi])
  dsimp only [quarterCenteredClosedResidual, quarterCenteredResidual] at h ⊢
  linarith only [h, hc]

end PseudoPrime.PrimeTestBounds.MillerRabin
