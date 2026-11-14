/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.LogTaylorBounds
public import PseudoPrime.Analysis.RoundedEulerProduct

/-! # Rational logarithm certificates for the height-100 grid -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- A rounded rational approximation to `log n`, computed from the upper
Taylor bound at the next power of two. It is used as input to the grid
exponential evaluator; no list lookup or external table is involved. -/
def gridLogApprox (n : ℕ) : ℚ :=
  Analysis.rationalGridFloor (10 ^ 9) (Analysis.rationalLogUpper n (Nat.log2 n + 1) 32)

/-- Check that the rational logarithm approximation lies in `[0,7]` and
that the Taylor interval encloses it within `10⁻⁷`. The result is decidable
using rational arithmetic and is shared by all 129 grid points. -/
def gridLogCheck (n : ℕ) : Bool :=
  decide (0 ≤ gridLogApprox n ∧ gridLogApprox n ≤ 7) &&
    Analysis.rationalLogIntervalCheck n (Nat.log2 n + 1) 32 (gridLogApprox n - 1 / 10000000)
      (gridLogApprox n + 1 / 10000000)

/-- A successful rational check bounds `log n` by the rounded value within
`10⁻⁷` and gives the nonnegativity and size hypotheses for exponentiation. -/
theorem grid_log_check_sound (n : ℕ) (h : gridLogCheck n = true) :
    0 ≤ gridLogApprox n ∧
      gridLogApprox n ≤ 7 ∧ |Real.log n - (gridLogApprox n : ℝ)| ≤ 1 / 10000000 := by
  have hh := Bool.and_eq_true_iff.mp h
  have hq : 0 ≤ gridLogApprox n ∧ gridLogApprox n ≤ 7 := of_decide_eq_true hh.1
  have hl := Analysis.rationalLogIntervalCheck_sound hh.2
  simp only [Rat.cast_natCast, Rat.cast_sub, Rat.cast_add, Rat.cast_div, Rat.cast_one,
    Rat.cast_ofNat] at hl
  refine ⟨hq.1, hq.2, abs_le.mpr ?_⟩
  constructor <;> linarith only [hl.1, hl.2]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
