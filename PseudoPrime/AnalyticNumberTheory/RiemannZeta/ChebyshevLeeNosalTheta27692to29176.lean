/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta27692to29176Calc

/-! # Lee–Nosal theta bound on the interval from 27692 to 29176 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The checked batch proves the Lee–Nosal theta estimate on `[27692, 29176)`. -/
theorem theta_lee_nosal_27692_29176 {x : ℝ} (ha : 27692 ≤ x) (hb : x < 29176) :
    |Chebyshev.theta x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  exact
    lee_nosal_chain_sound Chebyshev.theta_mono Chebyshev.theta_eq_theta_coe_floor theta27692_check
      theta27692_lower theta27692_upper theta27692_a theta27692_b ha hb

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
