/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta6204to6824Calc

/-! # Lee–Nosal theta bound on the interval from 6204 to 6824 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The checked batch proves the Lee–Nosal theta estimate on `[6204, 6824)`. -/
theorem theta_lee_nosal_6204_6824 {x : ℝ} (ha : 6204 ≤ x) (hb : x < 6824) :
    |Chebyshev.theta x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  exact
    lee_nosal_chain_sound Chebyshev.theta_mono Chebyshev.theta_eq_theta_coe_floor theta6204_check
      theta6204_lower theta6204_upper theta6204_a theta6204_b ha hb

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
