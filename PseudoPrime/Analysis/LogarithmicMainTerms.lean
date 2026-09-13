/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# Elementary main terms in logarithmic and reciprocal residue formulas

These real functions contain the logarithmic, Euler--Mascheroni, and pi terms in the odd and
even residue formulas. Their definitions impose no character, parity, or lower-cutoff assumption.
Quantitative estimates for a chosen cutoff belong to the modules that use these expressions.
-/

namespace PseudoPrime.Analysis

/-- The odd-parity main term `π²/8 - (log 2 + γ/2) log x` in logarithmic residue formulas. -/
noncomputable def primitiveLogOddMainError (x : ℝ) : ℝ :=
  Real.pi ^ 2 / 8 - (Real.log 2 + Real.eulerMascheroniConstant / 2) * Real.log x

/-- The even-parity main term `π²/24 - (γ/2) log x - (1/2)(log x)²`
in logarithmic residue formulas. -/
noncomputable def primitiveLogEvenMainError (x : ℝ) : ℝ :=
  Real.pi ^ 2 / 24 - (Real.eulerMascheroniConstant / 2) * Real.log x - (1 / 2) * Real.log x ^ 2

/-- The odd-parity main term `-(γ/2)(1 - 1/x) + log 2 / x` in reciprocal residue formulas. -/
noncomputable def primitiveReciprocalOddMainError (x : ℝ) : ℝ :=
  -(Real.eulerMascheroniConstant / 2) * (1 - 1 / x) + Real.log 2 / x

/-- The even-parity main term `-log 2 - (γ/2)(1 - 1/x) + (log x + 1) / x`
in reciprocal residue formulas. -/
noncomputable def primitiveReciprocalEvenMainError (x : ℝ) : ℝ :=
  -Real.log 2 - (Real.eulerMascheroniConstant / 2) * (1 - 1 / x) + (Real.log x + 1) / x

end PseudoPrime.Analysis
