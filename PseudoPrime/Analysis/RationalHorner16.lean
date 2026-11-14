/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ScaledRationalExp

/-! # Horner evaluation of rational exponential polynomials -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Compute a truncated exponential polynomial by a backward Horner recurrence. The pair `z`
is the rational complex argument, `k` is the remaining depth, and `j` is the denominator offset.
The endpoint evaluator uses depth 15 and offset zero for its 16-term Taylor polynomial. -/
def rationalExpHorner (z : ℚ × ℚ) : ℕ → ℕ → ℚ × ℚ
  | 0, _ => (1, 0)
  | k + 1, j =>
    rationalComplexAdd (1, 0)
      (rationalComplexScale (1 / (j + 1 : ℚ))
        (rationalComplexMul z (rationalExpHorner z k (j + 1))))

/-- Use the 16-term Horner polynomial and rounded squaring to approximate `exp(i*v)`.
The grid `G` and number of squarings `k` have the same meaning as in `rationalScaledPhase`. -/
def rationalHornerPhase16 (G : ℕ) (v : ℚ) (k : ℕ) : ℚ × ℚ :=
  rationalRoundedSquareIter G (rationalComplexRound G (rationalExpHorner (0, v / (2 : ℚ) ^ k) 15 0))
    k

/-- Use the 16-term Horner polynomial and rounded squaring to approximate `exp(v)`.
The grid `G` and number of squarings `k` match `rationalScaledRealExp`. -/
def rationalHornerRealExp16 (G : ℕ) (v : ℚ) (k : ℕ) : ℚ × ℚ :=
  rationalRoundedSquareIter G (rationalComplexRound G (rationalExpHorner (v / (2 : ℚ) ^ k, 0) 15 0))
    k

end PseudoPrime.Analysis
