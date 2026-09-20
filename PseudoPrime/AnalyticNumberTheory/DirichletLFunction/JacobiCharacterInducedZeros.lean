/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.GRH.Definition
import PseudoPrime.NumberTheory.PrimitiveJacobiCharacter
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.InducedZeros
import Mathlib.NumberTheory.DirichletCharacter.Bounds

/-!
# Zeros of induced Dirichlet L-functions

The finite Euler factors introduced by changing the level of a Dirichlet character do not vanish
in the right half-plane.  Hence a zero there of an induced L-function is already a zero of the
primitive L-function that induces it.
-/

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/--
For odd nonsquare `n` with nonzero `4 * n`, a zero in the right half-plane of the quadratic
character at level `4 * n` is a zero of its associated primitive character. Use the
change-level identity and nonvanishing of the added Euler factors.
-/
theorem induced_zero_of_rightHalfPlane_is_primitive_zero (n : ℕ) (hn : Odd n) (hns : ¬IsSquare n)
    [NeZero (4 * n)] {s : ℂ}
    (hszero : (NumberTheory.complexQuadraticCharacter n hn).LFunction s = 0) (hs : 0 < s.re) :
    (NumberTheory.primitiveQuadraticCharacter n hn).LFunction s = 0 := by
  have hlevel :=
    DirichletCharacter.changeLevel_primitiveCharacter (NumberTheory.complexQuadraticCharacter n hn)
  rw [← hlevel] at hszero
  exact
    changeLevel_zero_of_rightHalfPlane _ _
      (NumberTheory.primitiveQuadraticCharacter_ne_one_of_not_square n hn hns) hszero hs

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
