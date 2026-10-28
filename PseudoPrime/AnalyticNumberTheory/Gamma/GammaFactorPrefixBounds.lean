/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Gamma.DigammaPrefixBounds
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaFactorNumericalBounds

/-! # Finite-prefix Gamma-factor allowances

A lower real Gamma argument and a reciprocal-prefix length determine the explicit bound.
Both parity shifts retain the same allowance at each resolvent node.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Gamma

/-- The maximum of 3/10 and the correction inferred from m reciprocal-difference terms
 at lower argument R. The 3/10 term controls the upper digamma endpoint.
 This defines a rational per-node allowance for real Gamma factors. -/
noncomputable def gammaPrefixAllowance (R : ℝ) (m : ℕ) : ℝ :=
  max (3 / 10 : ℝ) ((159 / 50 - ∑ k ∈ Finset.range m, (1 / ((1 / 2 : ℝ) + k) - 1 / (R + k))) / 2)

end PseudoPrime.AnalyticNumberTheory.Gamma
