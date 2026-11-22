/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighMillion

/-! # The unconditional Chebyshev psi bound with coefficient 47/50 -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- For every real `x` in `[11, 1000000]`, the normalized psi error is at most `47 / 50`.
The joint certificate covers the low cells and transfers the stronger
coefficient `81 / 100` from 17 onward. -/
theorem psi94_million {x : ℝ} (hx : 11 ≤ x) (hx' : x ≤ 1000000) :
    |Chebyshev.psi x - x| / Real.sqrt x ≤ (47 / 50 : ℝ) := by
  apply (div_le_iff₀ (Real.sqrt_pos.2 (by linarith only [hx]))).2
  exact Cert.Chebyshev.Joint.psi_94_of_segment Cert.Chebyshev.Joint.high_million hx hx'

end PseudoPrime.AnalyticNumberTheory.Arithmetic
