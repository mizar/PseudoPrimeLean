/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt1423
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt1510
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt1522
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrtGroup01
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrtGroup02
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrtGroup03
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrtGroup04
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrtGroup05
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrtGroup06
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrtGroup07
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrtGroup08
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrtGroup09
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrtGroup10
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrtGroup11
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrtGroup12
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrtGroup13

/-! # Finite four-fifths square-root psi error through one million -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- The thirteen independent interval groups compose from 1539 to 1000001. -/
private theorem walk_segment :
    PsiSqrtSegment 1000000000000
      ⟨1539, 7338887595015, 7338892225039, 1530963112671469, 1531658116819066⟩
      ⟨1000001, 13815510503107, 13815840571449, 999586234305296029, 999612447035773994⟩ := by
  exact
    (psi_sqrt_segment_comp
      (psi_sqrt_segment_comp
        (psi_sqrt_segment_comp (psi_sqrt_segment_comp psi_sqrt_group01 psi_sqrt_group02)
          (psi_sqrt_segment_comp psi_sqrt_group03 psi_sqrt_group04))
        (psi_sqrt_segment_comp (psi_sqrt_segment_comp psi_sqrt_group05 psi_sqrt_group06)
          (psi_sqrt_segment_comp psi_sqrt_group07 psi_sqrt_group08)))
      (psi_sqrt_segment_comp
        (psi_sqrt_segment_comp (psi_sqrt_segment_comp psi_sqrt_group09 psi_sqrt_group10)
          (psi_sqrt_segment_comp psi_sqrt_group11 psi_sqrt_group12))
        psi_sqrt_group13))

/-- For every real `x` with `1423 ≤ x ≤ 1000000`, the Chebyshev psi error is
at most four fifths of `sqrt x`. Independently verified finite intervals are
combined into thirteen intermediate groups before this final interval. -/
theorem psi_four_fifths_1423_million {x : ℝ} (ha : 1423 ≤ x) (hb : x ≤ 1000000) :
    |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x := by
  by_cases h : x < 1510
  · exact psi_four_fifths_1423_1510 ha h
  · by_cases h' : x < 1523
    · exact psi_four_fifths_1510_1523 (le_of_not_gt h) h'
    · by_cases h'' : x < 1539
      · exact psi_four_fifths_1522_1540 (by linarith only [h']) (by linarith only [h''])
      · apply (walk_segment psi_walk_1539_valid).2 x (le_of_not_gt h'')
        change x < (1000001 : ℝ)
        linarith only [hb]

/-- For every real `x` from 1423 through 1000000, the normalized Chebyshev ψ error is at most
`4 / 5`. Divide the existing unconditional square-root error bound by the positive square root. -/
theorem psi_error_le_four_fifths_million {x : ℝ} (hx : 1423 ≤ x) (hx' : x ≤ 1000000) :
    |Chebyshev.psi x - x| / Real.sqrt x ≤ (4 / 5 : ℝ) := by
  have hpos : 0 < x := lt_of_lt_of_le (by norm_num only) hx
  exact
    (div_le_iff₀ (Real.sqrt_pos.2 hpos)).2
      (psi_four_fifths_1423_million hx hx')

end PseudoPrime.AnalyticNumberTheory.Arithmetic
