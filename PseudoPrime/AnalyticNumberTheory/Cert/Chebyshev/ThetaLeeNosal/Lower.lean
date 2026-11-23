/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.High
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaDirectRange
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaMiddlePhase
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaRestartRange
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaGapRange
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaAnalyticOverlap

/-! # Global lower Lee–Nosal bound for theta -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

/-- Under RH, the lower Lee–Nosal estimate for theta holds for every real x at least 2657.
The signed middle phase supplies the entrance estimate for the final finite gap. -/
theorem theta_lower_lee_nosal_of_RH (hRH : RiemannHypothesis) {x : ℝ} (hx : 2657 ≤ x) :
    (x - Chebyshev.theta x) / Real.sqrt x ≤
      Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi) := by
  rcases le_total x 3593341184 with hlo | hlo
  · exact theta_lower_2657_3593341184 hx hlo
  rcases le_total x 7657341184 with hmid | hmid
  · exact theta_lower_middle_phase hRH hlo hmid
  rcases le_total x 7886980184 with h | h
  · exact (theta_gap_7886980184 (theta_restart_7657341184 hRH)).2 x hmid h
  rcases le_total x 8000000000 with h8 | h8
  · exact theta_lower_analytic_overlap hRH h h8
  · exact theta_lower_eight_billion hRH h8

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
