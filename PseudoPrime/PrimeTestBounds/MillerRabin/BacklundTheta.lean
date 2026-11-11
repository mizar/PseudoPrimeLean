/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Gamma.EulerLogSeries

/-! # Normalized Gamma phase for the Backlund argument -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The Riemann–Siegel Gamma phase using the analytic Euler logarithm of
Gamma, with the `π` factor removed. It is defined for every real height;
the intended estimates use positive heights. -/
noncomputable def backlundTheta (t : ℝ) : ℝ :=
  (AnalyticNumberTheory.Gamma.logGammaSeries
        (((1 / 4 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I)).im -
    (t / 2) * Real.log Real.pi

/-- The elementary main term of the Gamma phase at height `t`. It is the
phase appearing in the Riemann–von Mangoldt main term. -/
noncomputable def backlundThetaMain (t : ℝ) : ℝ :=
  t / 2 * Real.log (t / (2 * Real.pi)) - t / 2 - Real.pi / 8

/-- The normalized discrepancy between the Gamma phase and its elementary
main term. This is the error inserted into the coarse zero-count identity. -/
noncomputable def backlundThetaError (t : ℝ) : ℝ :=
  (backlundTheta t - backlundThetaMain t) / Real.pi

end PseudoPrime.PrimeTestBounds.MillerRabin
