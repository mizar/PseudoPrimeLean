/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta24376to26035Calc

/-! # Lee–Nosal theta bound on the interval from 24376 to 26035 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The checked batch proves the Lee–Nosal theta estimate on `[24376, 26035)`. -/
theorem theta_lee_nosal_24376_26035 {x : ℝ} (ha : 24376 ≤ x) (hb : x < 26035) :
    |Chebyshev.theta x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  exact
    lee_nosal_chain_sound Chebyshev.theta_mono Chebyshev.theta_eq_theta_coe_floor theta24376_check
      theta24376_lower theta24376_upper theta24376_a theta24376_b ha hb

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
