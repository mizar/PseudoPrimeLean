/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ScaledRationalPhase

/-! # Rational Euler–Maclaurin correction -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Compute the inverse of a rational complex pair by its squared norm, including at zero.
This is used to evaluate the pole term in the endpoint correction exactly. -/
def endpointComplexInv (z : ℚ × ℚ) : ℚ × ℚ :=
  (z.1 / (z.1 ^ 2 + z.2 ^ 2), -z.2 / (z.1 ^ 2 + z.2 ^ 2))

/-- Compute the grouped four-term Euler–Maclaurin correction as a rational complex pair.
The rational input is the ordinate, and all products and inverses are exact. -/
def endpointCoefficient (t : ℚ) : ℚ × ℚ :=
  let s : ℚ × ℚ := (1 / 2, t)
  let p3 :=
    Analysis.rationalComplexMul (Analysis.rationalComplexMul s (1 / 2 + 1, t)) (1 / 2 + 2, t)
  let p5 :=
    Analysis.rationalComplexMul (Analysis.rationalComplexMul p3 (1 / 2 + 3, t)) (1 / 2 + 4, t)
  let p7 :=
    Analysis.rationalComplexMul (Analysis.rationalComplexMul p5 (1 / 2 + 5, t)) (1 / 2 + 6, t)
  Analysis.rationalComplexAdd (Analysis.rationalComplexScale 128 (endpointComplexInv (-1 / 2, t)))
    (Analysis.rationalComplexAdd (1 / 2, 0)
      (Analysis.rationalComplexAdd (Analysis.rationalComplexScale (1 / (12 * 128)) s)
        (Analysis.rationalComplexAdd (Analysis.rationalComplexScale (-1 / (720 * 128 ^ 3)) p3)
          (Analysis.rationalComplexAdd (Analysis.rationalComplexScale (1 / (30240 * 128 ^ 5)) p5)
            (Analysis.rationalComplexScale (-1 / (1209600 * 128 ^ 7)) p7)))))

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
