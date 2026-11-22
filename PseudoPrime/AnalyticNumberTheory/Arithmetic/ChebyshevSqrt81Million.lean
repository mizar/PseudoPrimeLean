/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt1423toMillion
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighMillion

/-! # Reduction of the coefficient-81/100 psi bound below one million -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

private theorem psi81_initial {x : ℝ} (hx : 17 ≤ x) (hr : x < 101) :
    |Chebyshev.psi x - x| / Real.sqrt x ≤ (81 / 100 : ℝ) := by
  apply (div_le_iff₀ (Real.sqrt_pos.2 (by linarith only [hx]))).2
  exact Cert.Chebyshev.Joint.low_prefix.2.2 x hx hr

/-- Every real `x` in `[1423, 1000000]` satisfies the `81 / 100` normalized psi error bound.
The existing unconditional `4 / 5` estimate is stronger on this interval. -/
theorem psi81_of_1423_le {x : ℝ} (hx : 1423 ≤ x) (hx' : x ≤ 1000000) :
    |Chebyshev.psi x - x| / Real.sqrt x ≤ (81 / 100 : ℝ) := by
  exact (psi_error_le_four_fifths_million hx hx').trans (by norm_num only)

/-- The `81 / 100` estimate on `[17, 1000000]` follows from its missing half-open low interval
`[17, 1423)`. The remaining interval uses the existing unconditional `4 / 5` estimate. -/
theorem psi81_million_of_small
    (hsmall : ∀ x : ℝ, 17 ≤ x → x < 1423 → |Chebyshev.psi x - x| / Real.sqrt x ≤ (81 / 100 : ℝ))
    {x : ℝ} (hx : 17 ≤ x) (hx' : x ≤ 1000000) :
    |Chebyshev.psi x - x| / Real.sqrt x ≤ (81 / 100 : ℝ) := by
  by_cases h : x < 1423
  · exact hsmall x hx h
  · exact psi81_of_1423_le (le_of_not_gt h) hx'

/-- The `81 / 100` estimate on `[17, 1000000]` follows from its remaining interval
`[23, 1423)`. Independent internal certificates prove `[17, 23)`, and the existing
unconditional `4 / 5` estimate covers the range from 1423 onward. -/
theorem psi81_million_of_23_1423
    (hsmall : ∀ x : ℝ, 23 ≤ x → x < 1423 → |Chebyshev.psi x - x| / Real.sqrt x ≤ (81 / 100 : ℝ))
    {x : ℝ} (hx : 17 ≤ x) (hx' : x ≤ 1000000) :
    |Chebyshev.psi x - x| / Real.sqrt x ≤ (81 / 100 : ℝ) := by
  by_cases h : x < 23
  · exact psi81_initial hx (by linarith only [h])
  · by_cases h' : x < 1423
    · exact hsmall x (le_of_not_gt h) h'
    · exact psi81_of_1423_le (le_of_not_gt h') hx'

/-- The `81 / 100` estimate on `[17, 1000000]` follows from its remaining interval
`[26, 1423)`. The earlier and later ranges are supplied by unconditional certificates. -/
theorem psi81_million_of_26_1423
    (hsmall : ∀ x : ℝ, 26 ≤ x → x < 1423 → |Chebyshev.psi x - x| / Real.sqrt x ≤ (81 / 100 : ℝ))
    {x : ℝ} (hx : 17 ≤ x) (hx' : x ≤ 1000000) :
    |Chebyshev.psi x - x| / Real.sqrt x ≤ (81 / 100 : ℝ) := by
  by_cases h : x < 26
  · exact psi81_initial hx (by linarith only [h])
  · by_cases h' : x < 1423
    · exact hsmall x (le_of_not_gt h) h'
    · exact psi81_of_1423_le (le_of_not_gt h') hx'

/-- The joint finite certificate gives the normalized psi estimate from 17 to one million.
Divide its absolute-error estimate by the positive square root of the input. -/
theorem psi81_million {x : ℝ} (hx : 17 ≤ x) (hx' : x ≤ 1000000) :
    |Chebyshev.psi x - x| / Real.sqrt x ≤ (81 / 100 : ℝ) := by
  apply (div_le_iff₀ (Real.sqrt_pos.2 (by linarith only [hx]))).2
  exact Cert.Chebyshev.Joint.psi_81_of_segment Cert.Chebyshev.Joint.high_million hx hx'

end PseudoPrime.AnalyticNumberTheory.Arithmetic
