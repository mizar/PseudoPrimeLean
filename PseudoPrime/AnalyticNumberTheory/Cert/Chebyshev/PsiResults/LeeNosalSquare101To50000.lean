/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevLeeNosalSquare
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevPsiLeeNosalMillion

/-! # Finite psi square-logarithmic bound -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiResults

/-- For `101 ≤ x ≤ 50000`, the Chebyshev psi error is at most
`sqrt x * log x ^ 2 / 12`. The certified Lee–Nosal interval gives the sharper input. -/
theorem square_bound_101_50000 {x : ℝ} (ha : 101 ≤ x) (hb : x ≤ 50000) :
    |Chebyshev.psi x - x| ≤ Real.sqrt x * (Real.log x ^ 2 / 12) := by
  have hx : Real.exp 1 ≤ x := Real.exp_one_lt_three.le.trans (by linarith only [ha])
  exact
    (Arithmetic.psi_lee_nosal_101_million ha (by linarith only [hb])).trans
      (Arithmetic.lee_nosal_le_square_twelve hx)

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiResults
