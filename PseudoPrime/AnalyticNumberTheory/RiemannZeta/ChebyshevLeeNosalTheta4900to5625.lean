/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta4900to5625Calc

/-! # Lee–Nosal theta bound on the interval from 4900 to 5625 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The checked batch proves the Lee–Nosal theta estimate on `[4900, 5625)`. -/
theorem theta_lee_nosal_4900_5625 {x : ℝ} (ha : 4900 ≤ x) (hb : x < 5625) :
    |Chebyshev.theta x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  exact
    lee_nosal_chain_sound Chebyshev.theta_mono Chebyshev.theta_eq_theta_coe_floor theta4900_check
      theta4900_lower theta4900_upper theta4900_a theta4900_b ha hb

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
