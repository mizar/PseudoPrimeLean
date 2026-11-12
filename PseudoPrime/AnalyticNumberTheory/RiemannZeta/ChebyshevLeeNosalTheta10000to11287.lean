/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta10000to11287Calc

/-! # Lee–Nosal theta bound on the interval from 10000 to 11287 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The checked batch proves the Lee–Nosal theta estimate on `[10000, 11287)`. -/
theorem theta_lee_nosal_10000_11287 {x : ℝ} (ha : 10000 ≤ x) (hb : x < 11287) :
    |Chebyshev.theta x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  exact
    lee_nosal_chain_sound Chebyshev.theta_mono Chebyshev.theta_eq_theta_coe_floor theta10000_check
      theta10000_lower theta10000_upper theta10000_a theta10000_b ha hb

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
