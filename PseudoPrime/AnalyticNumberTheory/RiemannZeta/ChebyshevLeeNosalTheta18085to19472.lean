/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta18085to19472Calc

/-! # Lee–Nosal theta bound on the interval from 18085 to 19472 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The checked batch proves the Lee–Nosal theta estimate on `[18085, 19472)`. -/
theorem theta_lee_nosal_18085_19472 {x : ℝ} (ha : 18085 ≤ x) (hb : x < 19472) :
    |Chebyshev.theta x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  exact
    lee_nosal_chain_sound Chebyshev.theta_mono Chebyshev.theta_eq_theta_coe_floor theta18085_check
      theta18085_lower theta18085_upper theta18085_a theta18085_b ha hb

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
