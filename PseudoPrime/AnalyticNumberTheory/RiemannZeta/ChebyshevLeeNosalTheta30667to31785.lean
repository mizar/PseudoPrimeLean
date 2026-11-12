/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta30667to31785Calc

/-! # Lee–Nosal theta bound on the interval from 30667 to 31785 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The checked batch proves the Lee–Nosal theta estimate on `[30667, 31785)`. -/
theorem theta_lee_nosal_30667_31785 {x : ℝ} (ha : 30667 ≤ x) (hb : x < 31785) :
    |Chebyshev.theta x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  exact
    lee_nosal_chain_sound Chebyshev.theta_mono Chebyshev.theta_eq_theta_coe_floor theta30667_check
      theta30667_lower theta30667_upper theta30667_a theta30667_b ha hb

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
