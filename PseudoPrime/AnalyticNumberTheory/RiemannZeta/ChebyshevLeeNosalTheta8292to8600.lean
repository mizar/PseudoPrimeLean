/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta8292to8600Calc

/-! # Lee–Nosal theta bound on the interval from 8292 to 8600 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The checked batch proves the Lee–Nosal theta estimate on `[8292, 8600)`. -/
theorem theta_lee_nosal_8292_8600 {x : ℝ} (ha : 8292 ≤ x) (hb : x < 8600) :
    |Chebyshev.theta x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  exact
    lee_nosal_chain_sound Chebyshev.theta_mono Chebyshev.theta_eq_theta_coe_floor theta8292_check
      theta8292_lower theta8292_upper theta8292_a theta8292_b ha hb

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
