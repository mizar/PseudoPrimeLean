/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta12035to12995Calc

/-! # Lee–Nosal theta bound on the interval from 12035 to 12995 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The checked batch proves the Lee–Nosal theta estimate on `[12035, 12995)`. -/
theorem theta_lee_nosal_12035_12995 {x : ℝ} (ha : 12035 ≤ x) (hb : x < 12995) :
    |Chebyshev.theta x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  exact
    lee_nosal_chain_sound Chebyshev.theta_mono Chebyshev.theta_eq_theta_coe_floor theta12035_check
      theta12035_lower theta12035_upper theta12035_a theta12035_b ha hb

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
