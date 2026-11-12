/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta22356to24376Calc

/-! # Lee–Nosal theta bound on the interval from 22356 to 24376 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The checked batch proves the Lee–Nosal theta estimate on `[22356, 24376)`. -/
theorem theta_lee_nosal_22356_24376 {x : ℝ} (ha : 22356 ≤ x) (hb : x < 24376) :
    |Chebyshev.theta x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  exact
    lee_nosal_chain_sound Chebyshev.theta_mono Chebyshev.theta_eq_theta_coe_floor theta22356_check
      theta22356_lower theta22356_upper theta22356_a theta22356_b ha hb

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
