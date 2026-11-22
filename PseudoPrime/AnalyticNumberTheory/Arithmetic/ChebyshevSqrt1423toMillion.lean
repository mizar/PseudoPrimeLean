/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighMillion

/-! # Finite four-fifths square-root psi error through one million -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- For every real `x` with `1423 ≤ x ≤ 1000000`, the Chebyshev psi error is
at most four fifths of `sqrt x`. The joint certificate combines the low intervals, high batches and
the closed million endpoint. -/
theorem psi_four_fifths_1423_million {x : ℝ} (ha : 1423 ≤ x) (hb : x ≤ 1000000) :
    |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x := by
  exact Cert.Chebyshev.Joint.psi_four_fifths_of_segment Cert.Chebyshev.Joint.high_million ha hb

/-- For every real `x` from 1423 through 1000000, the normalized Chebyshev ψ error is at most
`4 / 5`. Divide the existing unconditional square-root error bound by the positive square root. -/
theorem psi_error_le_four_fifths_million {x : ℝ} (hx : 1423 ≤ x) (hx' : x ≤ 1000000) :
    |Chebyshev.psi x - x| / Real.sqrt x ≤ (4 / 5 : ℝ) := by
  have hpos : 0 < x := lt_of_lt_of_le (by norm_num only) hx
  exact (div_le_iff₀ (Real.sqrt_pos.2 hpos)).2 (psi_four_fifths_1423_million hx hx')

end PseudoPrime.AnalyticNumberTheory.Arithmetic
