/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaSignedEulerSeries
public import PseudoPrime.Analysis.ExponentialRampLocalCorrection

/-! # Actual local prime costs with arbitrary finite positive-power prefixes -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Actual local character loss at a prime p, using every positive Euler
power selected by K and the full signed ramp series at the same local value.
Even exponents are included. This is the cost used by general prefix grouping. -/
noncomputable def gammaActualPrimeLocalCost {f : ℕ} (χ : DirichletCharacter ℂ f) (p : ℕ)
    (K : Finset ℕ) (x : ℝ) : ℝ :=
  (∑ k ∈ K, (1 - (χ (p ^ (k + 1))).re) * gammaResolventMangoldtWeight (p ^ (k + 1))) +
    Real.log p *
      ((∑' k : ℕ, exponentialRampLocalCorrection (χ p) ((p : ℝ) ^ (k + 1) / x) (k + 1)) /
        Real.sqrt x)

end PseudoPrime.Analysis
