/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta7318to7776Calc

/-! # Lee–Nosal theta bound on the interval from 7318 to 7776 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The checked batch proves the Lee–Nosal theta estimate on `[7318, 7776)`. -/
theorem theta_lee_nosal_7318_7776 {x : ℝ} (ha : 7318 ≤ x) (hb : x < 7776) :
    |Chebyshev.theta x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  exact
    lee_nosal_chain_sound Chebyshev.theta_mono Chebyshev.theta_eq_theta_coe_floor theta7318_check
      theta7318_lower theta7318_upper theta7318_a theta7318_b ha hb

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
