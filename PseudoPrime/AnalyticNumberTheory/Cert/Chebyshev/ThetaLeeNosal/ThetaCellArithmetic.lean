/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.LogTaylorBounds

/-! # Rational upper and lower estimates for a shifted theta phase cell -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

/-- Residual lower bound after replacing the two logarithms by rational Taylor bounds
and pi by outward decimal bounds. The log arguments in the middle band lie in (0,64). -/
def phaseCellSlack (a b u v : ℚ) : ℚ :=
  let piLo := 6283 / 2000
  let piHi := 3927 / 1250
  let q := 2 * b / 7 - 2 / 3
  let A := b / 2 - Analysis.rationalLogLower (piLo * q) 5 32
  let target := a * (a - Analysis.rationalLogUpper a 5 32) / (8 * piHi)
  let head := max 0 (max u v) + 3611 * (b - a + 1 / 2800) ^ 2 / 8
  target - (q / 2 + head + (A ^ 2 + 3 / 2 * A + 3 / 2) / (2 * piLo) - 579 / 5000)

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
