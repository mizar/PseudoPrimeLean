/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # The real paired Euler term -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- The paired real-axis term Λ(m)(1+Re χ(m))/m^σ.
For σ>1 these terms converge absolutely, and norm-bounded character values
make every term nonnegative. Their sum retains both logarithmic derivatives. -/
noncomputable def realPairedEulerTerm {q : ℕ} (χ : DirichletCharacter ℂ q) (σ : ℝ) (m : ℕ) : ℝ :=
  (1 + (χ m).re) * ArithmeticFunction.vonMangoldt m / (m : ℝ) ^ σ

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
