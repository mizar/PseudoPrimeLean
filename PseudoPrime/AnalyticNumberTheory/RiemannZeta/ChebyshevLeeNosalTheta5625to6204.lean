/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta5625to6204Calc

/-! # Lee–Nosal theta bound on the interval from 5625 to 6204 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The checked batch proves the Lee–Nosal theta estimate on `[5625, 6204)`. -/
theorem theta_lee_nosal_5625_6204 {x : ℝ} (ha : 5625 ≤ x) (hb : x < 6204) :
    |Chebyshev.theta x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  exact
    lee_nosal_chain_sound Chebyshev.theta_mono Chebyshev.theta_eq_theta_coe_floor theta5625_check
      theta5625_lower theta5625_upper theta5625_a theta5625_b ha hb

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
