/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta26035to27692Calc

/-! # Lee–Nosal theta bound on the interval from 26035 to 27692 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The checked batch proves the Lee–Nosal theta estimate on `[26035, 27692)`. -/
theorem theta_lee_nosal_26035_27692 {x : ℝ} (ha : 26035 ≤ x) (hb : x < 27692) :
    |Chebyshev.theta x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  exact
    lee_nosal_chain_sound Chebyshev.theta_mono Chebyshev.theta_eq_theta_coe_floor theta26035_check
      theta26035_lower theta26035_upper theta26035_a theta26035_b ha hb

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
