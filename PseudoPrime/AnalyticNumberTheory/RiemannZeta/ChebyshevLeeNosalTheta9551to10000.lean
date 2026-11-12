/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta9551to10000Calc

/-! # Lee–Nosal theta bound on the interval from 9551 to 10000 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The checked batch proves the Lee–Nosal theta estimate on `[9551, 10000)`. -/
theorem theta_lee_nosal_9551_10000 {x : ℝ} (ha : 9551 ≤ x) (hb : x < 10000) :
    |Chebyshev.theta x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  exact
    lee_nosal_chain_sound Chebyshev.theta_mono Chebyshev.theta_eq_theta_coe_floor theta9551_check
      theta9551_lower theta9551_upper theta9551_a theta9551_b ha hb

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
