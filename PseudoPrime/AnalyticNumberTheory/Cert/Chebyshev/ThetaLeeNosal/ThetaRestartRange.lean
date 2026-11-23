/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaMiddlePhase
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaRestart7434389760
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaRestart7466389760
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaRestart7498389760
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaRestart7530389760
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaRestart7562389760
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaRestart7594389760
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaRestart7626389760
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaRestart7657341184

/-! # Assembly of the scalar restart transfers -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

/-- Propagate the signed phase entrance to the start of the finite gap under RH. -/
theorem theta_restart_7657341184 (hRH : RiemannHypothesis) :
    (((382790423425787 / 50000) : ℚ) : ℝ) ≤ Chebyshev.theta 7657341184 := by
  exact
    (Function.comp
        (Function.comp (Function.comp restart_window_7657341184 restart_window_7626389760)
          (Function.comp restart_window_7594389760 restart_window_7562389760))
        (Function.comp (Function.comp restart_window_7530389760 restart_window_7498389760)
          (Function.comp restart_window_7466389760 restart_window_7434389760)))
      (by simpa only [Rat.cast_ofNat] using theta_middle_restart hRH)

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
