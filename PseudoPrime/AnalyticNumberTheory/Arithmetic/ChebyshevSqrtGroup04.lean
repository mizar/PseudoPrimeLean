/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrtSegment
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt241539To246539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt246539To251539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt251539To256539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt256539To261539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt261539To266539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt266539To271539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt271539To276539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt276539To281539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt281539To286539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt286539To291539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt291539To296539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt296539To301539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt301539To306539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt306539To311539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt311539To316539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt316539To321539

/-! # Independent finite psi segment group 4 -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- Compose the checked intervals from 241539 to 321539; the source certificates
are consumed privately and this theorem contains no computational data. -/
theorem psi_sqrt_group04 :
    PsiSqrtSegment 1000000000000
      ⟨241539, 12394785553519, 12395113293239, 241458888585524096, 241466283392081990⟩
      ⟨321539, 12680873405640, 12681201740245, 321593111423271578, 321602600493553941⟩ := by
  exact
    (psi_sqrt_segment_comp
      (psi_sqrt_segment_comp
        (psi_sqrt_segment_comp
          (psi_sqrt_segment_comp psi_sqrt_segment_241539_246539 psi_sqrt_segment_246539_251539)
          (psi_sqrt_segment_comp psi_sqrt_segment_251539_256539 psi_sqrt_segment_256539_261539))
        (psi_sqrt_segment_comp
          (psi_sqrt_segment_comp psi_sqrt_segment_261539_266539 psi_sqrt_segment_266539_271539)
          (psi_sqrt_segment_comp psi_sqrt_segment_271539_276539 psi_sqrt_segment_276539_281539)))
      (psi_sqrt_segment_comp
        (psi_sqrt_segment_comp
          (psi_sqrt_segment_comp psi_sqrt_segment_281539_286539 psi_sqrt_segment_286539_291539)
          (psi_sqrt_segment_comp psi_sqrt_segment_291539_296539 psi_sqrt_segment_296539_301539))
        (psi_sqrt_segment_comp
          (psi_sqrt_segment_comp psi_sqrt_segment_301539_306539 psi_sqrt_segment_306539_311539)
          (psi_sqrt_segment_comp psi_sqrt_segment_311539_316539 psi_sqrt_segment_316539_321539))))

end PseudoPrime.AnalyticNumberTheory.Arithmetic
