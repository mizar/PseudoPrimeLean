/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta6824to7318Calc

/-! # Lee–Nosal theta bound on the interval from 6824 to 7318 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The checked batch proves the Lee–Nosal theta estimate on `[6824, 7318)`. -/
theorem theta_lee_nosal_6824_7318 {x : ℝ} (ha : 6824 ≤ x) (hb : x < 7318) :
    |Chebyshev.theta x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  exact
    lee_nosal_chain_sound Chebyshev.theta_mono Chebyshev.theta_eq_theta_coe_floor theta6824_check
      theta6824_lower theta6824_upper theta6824_a theta6824_b ha hb

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
