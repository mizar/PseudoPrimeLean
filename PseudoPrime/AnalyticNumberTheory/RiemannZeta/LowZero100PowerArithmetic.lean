/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ScaledRationalExp
public import PseudoPrime.Analysis.ScaledRationalPhase

/-! # Rational power evaluator for low-zero endpoints -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Compute a rounded rational complex approximation to
`exp(-(1/2 + it)q)` from rational inputs `t` and `q`. The real exponential
and phase use the same fixed grid and separately range-reduced Taylor sums;
the analytic error is proved in the consuming bounds module. -/
def endpointPowerApprox (t q : ℚ) : ℚ × ℚ :=
  Analysis.rationalComplexMul (Analysis.rationalScaledRealExp (10 ^ 15) (-(1 / 2 : ℚ) * q) 16 6)
    (Analysis.rationalScaledPhase (10 ^ 15) (-t * q) 16 11)

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
