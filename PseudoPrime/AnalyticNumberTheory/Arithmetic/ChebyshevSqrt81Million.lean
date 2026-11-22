/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt1423toMillion
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound.Psi81Low17To26
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound.Psi81Low26To88
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound.Psi81Low88To193
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound.Psi81Low193To348
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound.Psi81Low348To568
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound.Psi81Low568To815
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound.Psi81Low815To1109
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound.Psi81Low1109To1423

/-! # Reduction of the coefficient-81/100 psi bound below one million -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

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
  · exact Cert.Chebyshev.PsiSqrtBound.psi81_on_17_23 hx h
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
  · exact Cert.Chebyshev.PsiSqrtBound.psi81_on_17_26 hx h
  · by_cases h' : x < 1423
    · exact hsmall x (le_of_not_gt h) h'
    · exact psi81_of_1423_le (le_of_not_gt h') hx'

/-- The internal LCM certificates and the existing four-fifths bound give the
unconditional normalized psi estimate on the closed interval from 17 to one million. -/
theorem psi81_million {x : ℝ} (hx : 17 ≤ x) (hx' : x ≤ 1000000) :
    |Chebyshev.psi x - x| / Real.sqrt x ≤ (81 / 100 : ℝ) := by
  apply psi81_million_of_26_1423 _ hx hx'
  intro y ha hb
  by_cases h88 : y < 88
  · exact Cert.Chebyshev.PsiSqrtBound.psi81_on_26_88 ha h88
  by_cases h193 : y < 193
  · exact Cert.Chebyshev.PsiSqrtBound.psi81_on_88_193 (le_of_not_gt h88) h193
  by_cases h348 : y < 348
  · exact Cert.Chebyshev.PsiSqrtBound.psi81_on_193_348 (le_of_not_gt h193) h348
  by_cases h568 : y < 568
  · exact Cert.Chebyshev.PsiSqrtBound.psi81_on_348_568 (le_of_not_gt h348) h568
  by_cases h815 : y < 815
  · exact Cert.Chebyshev.PsiSqrtBound.psi81_on_568_815 (le_of_not_gt h568) h815
  by_cases h1109 : y < 1109
  · exact Cert.Chebyshev.PsiSqrtBound.psi81_on_815_1109 (le_of_not_gt h815) h1109
  exact Cert.Chebyshev.PsiSqrtBound.psi81_on_1109_1423 (le_of_not_gt h1109) hb

end PseudoPrime.AnalyticNumberTheory.Arithmetic
