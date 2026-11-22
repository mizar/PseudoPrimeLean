/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.EnvelopeTransfer
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.ClosedBands

/-! # Lee–Nosal coefficient certificates for the finite theta bands -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

/-- From 2657 onward the Lee–Nosal coefficient dominates 9/5. -/
theorem coefficient2657 {x : ℝ} (hx : 2657 ≤ x) :
    (9 / 5 : ℝ) ≤ Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi) := by
  exact
    coefficient_from_ticks (n := 2657) (m := 7880) (by decide) hx (by decide +kernel)
      (by norm_num only) (by norm_num only) (by norm_num only)

/-- From 3100 onward the Lee–Nosal coefficient dominates 19/10. -/
theorem coefficient3100 {x : ℝ} (hx : 3100 ≤ x) :
    (19 / 10 : ℝ) ≤ Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi) := by
  exact
    coefficient_from_ticks (n := 3100) (m := 8038) (by decide) hx (by decide +kernel)
      (by norm_num only) (by norm_num only) (by norm_num only)

/-- From 3500 onward the Lee–Nosal coefficient dominates 97/50. -/
theorem coefficient3500 {x : ℝ} (hx : 3500 ≤ x) :
    (97 / 50 : ℝ) ≤ Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi) := by
  exact
    coefficient_from_ticks (n := 3500) (m := 8160) (by decide) hx (by decide +kernel)
      (by norm_num only) (by norm_num only) (by norm_num only)

/-- The two finite theta bands imply the normalized Lee–Nosal estimate on [2657,3500]. -/
theorem theta_lee_nosal_2657_3500 {x : ℝ} (hl : 2657 ≤ x) (hr : x ≤ 3500) :
    |Chebyshev.theta x - x| / Real.sqrt x ≤
      Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi) := by
  have hx : 0 < x := by linarith only [hl]
  rcases le_total x 3100 with h | h
  · exact theta_ratio_of_coeff hx (thetaClosed3100 hl h) (coefficient2657 hl)
  · exact theta_ratio_of_coeff hx (thetaClosed3500 h hr) (coefficient3100 h)

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
