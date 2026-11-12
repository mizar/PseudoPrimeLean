/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta8600to8981Calc

/-! # Lee–Nosal theta bound on the interval from 8600 to 8981 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The checked batch proves the Lee–Nosal theta estimate on `[8600, 8981)`. -/
theorem theta_lee_nosal_8600_8981 {x : ℝ} (ha : 8600 ≤ x) (hb : x < 8981) :
    |Chebyshev.theta x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  exact
    lee_nosal_chain_sound Chebyshev.theta_mono Chebyshev.theta_eq_theta_coe_floor theta8600_check
      theta8600_lower theta8600_upper theta8600_a theta8600_b ha hb

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
