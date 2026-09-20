/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

import PseudoPrime.AnalyticNumberTheory.GRH.Definition
import PseudoPrime.NumberTheory.PrimitiveJacobiCharacter

/-!
# GRH specialization for primitive quadratic characters

This module keeps the quadratic-character consequence separate from the
general Dirichlet-character GRH definition and its open-strip interface.
-/

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- Input: GRH, an odd integer `n`, and a zero of the primitive character associated to
the quadratic character at level `4 * n`.
Output: the zero lies on the critical line when it has positive real part.
This is the quadratic-character specialization used by the analytic bounds.
-/
theorem grh_primitiveQuadraticCharacter_zero (hGRH : GRH.GeneralizedRiemannHypothesis) (n : ℕ)
    (hn : Odd n) (s : ℂ) (hszero : (NumberTheory.primitiveQuadraticCharacter n hn).LFunction s = 0)
    (hspos : 0 < s.re) : s.re = (1 : ℝ) / 2 := by
  exact
    hGRH.zero_re_eq_half _ (NumberTheory.primitiveQuadraticCharacter n hn)
      (NumberTheory.primitiveQuadraticCharacter_isPrimitive n hn) s hszero hspos

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
