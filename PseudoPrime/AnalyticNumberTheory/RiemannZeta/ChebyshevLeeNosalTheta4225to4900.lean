/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta4225to4900Calc

/-! # Lee–Nosal theta bound on the interval from 4225 to 4900 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The checked batch proves the Lee–Nosal theta estimate on `[4225, 4900)`. -/
theorem theta_lee_nosal_4225_4900 {x : ℝ} (ha : 4225 ≤ x) (hb : x < 4900) :
    |Chebyshev.theta x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  exact
    lee_nosal_chain_sound Chebyshev.theta_mono Chebyshev.theta_eq_theta_coe_floor theta4225_check
      theta4225_lower theta4225_upper theta4225_a theta4225_b ha hb

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
