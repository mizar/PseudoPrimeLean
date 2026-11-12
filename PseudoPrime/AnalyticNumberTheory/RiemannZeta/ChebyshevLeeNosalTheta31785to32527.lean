/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta31785to32527Calc

/-! # Lee–Nosal theta bound on the interval from 31785 to 32527 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The checked batch proves the Lee–Nosal theta estimate on `[31785, 32527)`. -/
theorem theta_lee_nosal_31785_32527 {x : ℝ} (ha : 31785 ≤ x) (hb : x < 32527) :
    |Chebyshev.theta x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  exact
    lee_nosal_chain_sound Chebyshev.theta_mono Chebyshev.theta_eq_theta_coe_floor theta31785_check
      theta31785_lower theta31785_upper theta31785_a theta31785_b ha hb

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
