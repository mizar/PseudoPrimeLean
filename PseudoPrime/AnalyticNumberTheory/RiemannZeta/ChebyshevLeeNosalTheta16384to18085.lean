/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta16384to18085Calc

/-! # Lee–Nosal theta bound on the interval from 16384 to 18085 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The checked batch proves the Lee–Nosal theta estimate on `[16384, 18085)`. -/
theorem theta_lee_nosal_16384_18085 {x : ℝ} (ha : 16384 ≤ x) (hb : x < 18085) :
    |Chebyshev.theta x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  exact
    lee_nosal_chain_sound Chebyshev.theta_mono Chebyshev.theta_eq_theta_coe_floor theta16384_check
      theta16384_lower theta16384_upper theta16384_a theta16384_b ha hb

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
