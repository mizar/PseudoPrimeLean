/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import Mathlib.NumberTheory.MulChar.Basic
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.Basic

/-!
# Quadratic self-duality of the completed Dirichlet L-function

Specialize the primitive functional equation using `χ⁻¹ = χ`. Further general
quadratic consequences are in `QuadraticFunctionalConsequences` in this same
analytic-number-theory layer.
-/

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/--
Input/assumptions: a primitive quadratic complex Dirichlet character.
Conclusion: its completed-`L` functional equation is self-dual, i.e. `χ⁻¹` is replaced by `χ`.
Content: `MulChar.IsQuadratic.inv` collapses `χ⁻¹ = χ` inside mathlib's primitive functional
equation.
-/
theorem completedLFunction_one_sub_of_isPrimitive_isQuadratic {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hquad : χ.IsQuadratic) (s : ℂ) :
    DirichletCharacter.completedLFunction χ (1 - s) =
      N ^ (s - 1 / 2) * DirichletCharacter.rootNumber χ *
        DirichletCharacter.completedLFunction χ s := by
  have h := hprimitive.completedLFunction_one_sub s
  rwa [hquad.inv] at h

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
