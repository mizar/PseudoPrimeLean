/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrtSegment
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt321539To326539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt326539To331539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt331539To336539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt336539To341539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt341539To346539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt346539To351539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt351539To356539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt356539To361539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt361539To366539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt366539To371539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt371539To376539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt376539To381539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt381539To386539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt386539To391539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt391539To396539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt396539To401539

/-! # Independent finite psi segment group 5 -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- Compose the checked intervals from 321539 to 401539; the source certificates
are consumed privately and this theorem contains no computational data. -/
theorem psi_sqrt_group05 :
    PsiSqrtSegment 1000000000000
      ⟨321539, 12680873405640, 12681201740245, 321593111423271578, 321602600493553941⟩
      ⟨401539, 12903059187373, 12903387911897, 401514061130819551, 401525600299097131⟩ := by
  exact
    (psi_sqrt_segment_comp
      (psi_sqrt_segment_comp
        (psi_sqrt_segment_comp
          (psi_sqrt_segment_comp psi_sqrt_segment_321539_326539 psi_sqrt_segment_326539_331539)
          (psi_sqrt_segment_comp psi_sqrt_segment_331539_336539 psi_sqrt_segment_336539_341539))
        (psi_sqrt_segment_comp
          (psi_sqrt_segment_comp psi_sqrt_segment_341539_346539 psi_sqrt_segment_346539_351539)
          (psi_sqrt_segment_comp psi_sqrt_segment_351539_356539 psi_sqrt_segment_356539_361539)))
      (psi_sqrt_segment_comp
        (psi_sqrt_segment_comp
          (psi_sqrt_segment_comp psi_sqrt_segment_361539_366539 psi_sqrt_segment_366539_371539)
          (psi_sqrt_segment_comp psi_sqrt_segment_371539_376539 psi_sqrt_segment_376539_381539))
        (psi_sqrt_segment_comp
          (psi_sqrt_segment_comp psi_sqrt_segment_381539_386539 psi_sqrt_segment_386539_391539)
          (psi_sqrt_segment_comp psi_sqrt_segment_391539_396539 psi_sqrt_segment_396539_401539))))

end PseudoPrime.AnalyticNumberTheory.Arithmetic
