/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta7776to8292Calc

/-! # Lee–Nosal theta bound on the interval from 7776 to 8292 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The checked batch proves the Lee–Nosal theta estimate on `[7776, 8292)`. -/
theorem theta_lee_nosal_7776_8292 {x : ℝ} (ha : 7776 ≤ x) (hb : x < 8292) :
    |Chebyshev.theta x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  exact
    lee_nosal_chain_sound Chebyshev.theta_mono Chebyshev.theta_eq_theta_coe_floor theta7776_check
      theta7776_lower theta7776_upper theta7776_a theta7776_b ha hb

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
