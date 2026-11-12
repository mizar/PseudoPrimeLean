/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta20880to22356Calc

/-! # Lee–Nosal theta bound on the interval from 20880 to 22356 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The checked batch proves the Lee–Nosal theta estimate on `[20880, 22356)`. -/
theorem theta_lee_nosal_20880_22356 {x : ℝ} (ha : 20880 ≤ x) (hb : x < 22356) :
    |Chebyshev.theta x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  exact
    lee_nosal_chain_sound Chebyshev.theta_mono Chebyshev.theta_eq_theta_coe_floor theta20880_check
      theta20880_lower theta20880_upper theta20880_a theta20880_b ha hb

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
