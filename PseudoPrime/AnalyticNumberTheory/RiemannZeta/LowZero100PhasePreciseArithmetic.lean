/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100PhaseArithmetic

/-! # Narrow rational phase logarithm checks -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Check a narrower interval around the computed phase logarithm. This optional rational
check is used when the endpoint sign margin requires more precision than the common bound. -/
def endpointPhasePreciseCheck (t : ℚ) : Bool :=
  let q := endpointPhaseArgument t
  Analysis.rationalLogIntervalCheck q (endpointPhaseScale q) 32
    (endpointPhaseLog t - 4 / 1000000000) (endpointPhaseLog t + 4 / 1000000000)

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
