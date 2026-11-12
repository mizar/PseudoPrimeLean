/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta14251to15058Calc

/-! # Lee–Nosal theta bound on the interval from 14251 to 15058 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The checked batch proves the Lee–Nosal theta estimate on `[14251, 15058)`. -/
theorem theta_lee_nosal_14251_15058 {x : ℝ} (ha : 14251 ≤ x) (hb : x < 15058) :
    |Chebyshev.theta x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  exact
    lee_nosal_chain_sound Chebyshev.theta_mono Chebyshev.theta_eq_theta_coe_floor theta14251_check
      theta14251_lower theta14251_upper theta14251_a theta14251_b ha hb

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
