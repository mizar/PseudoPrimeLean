/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta29176to30667Calc

/-! # Lee–Nosal theta bound on the interval from 29176 to 30667 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The checked batch proves the Lee–Nosal theta estimate on `[29176, 30667)`. -/
theorem theta_lee_nosal_29176_30667 {x : ℝ} (ha : 29176 ≤ x) (hb : x < 30667) :
    |Chebyshev.theta x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  exact
    lee_nosal_chain_sound Chebyshev.theta_mono Chebyshev.theta_eq_theta_coe_floor theta29176_check
      theta29176_lower theta29176_upper theta29176_a theta29176_b ha hb

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
