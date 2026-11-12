/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta8981to9551Calc

/-! # Lee–Nosal theta bound on the interval from 8981 to 9551 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The checked batch proves the Lee–Nosal theta estimate on `[8981, 9551)`. -/
theorem theta_lee_nosal_8981_9551 {x : ℝ} (ha : 8981 ≤ x) (hb : x < 9551) :
    |Chebyshev.theta x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  exact
    lee_nosal_chain_sound Chebyshev.theta_mono Chebyshev.theta_eq_theta_coe_floor theta8981_check
      theta8981_lower theta8981_upper theta8981_a theta8981_b ha hb

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
