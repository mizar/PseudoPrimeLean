/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighMillion

/-! # Unconditional finite Lee–Nosal theta bound through one million -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- On the closed real interval from 2657 through one million, the normalized theta error
is bounded by the Lee–Nosal logarithmic coefficient. The joint finite certificate supplies
the three coefficient bands and their exact endpoints. -/
theorem theta_lee_nosal_2657_million {x : ℝ} (hl : 2657 ≤ x) (hr : x ≤ 1000000) :
    |Chebyshev.theta x - x| / Real.sqrt x ≤
      Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi) := by
  exact Cert.Chebyshev.Joint.theta_million_of_segment Cert.Chebyshev.Joint.high_million hl hr

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
