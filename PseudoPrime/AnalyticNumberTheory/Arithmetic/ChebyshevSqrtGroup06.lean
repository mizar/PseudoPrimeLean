/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrtSegment
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt401539To406539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt406539To411539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt411539To416539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt416539To421539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt421539To426539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt426539To431539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt431539To436539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt436539To441539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt441539To446539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt446539To451539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt451539To456539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt456539To461539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt461539To466539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt466539To471539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt471539To476539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt476539To481539

/-! # Independent finite psi segment group 6 -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- Compose the checked intervals from 401539 to 481539; the source certificates
are consumed privately and this theorem contains no computational data. -/
theorem psi_sqrt_group06 :
    PsiSqrtSegment 1000000000000
      ⟨401539, 12903059187373, 12903387911897, 401514061130819551, 401525600299097131⟩
      ⟨481539, 13084741707750, 13085070719213, 481599420075311906, 481612984332317400⟩ := by
  exact
    (psi_sqrt_segment_comp
      (psi_sqrt_segment_comp
        (psi_sqrt_segment_comp
          (psi_sqrt_segment_comp psi_sqrt_segment_401539_406539 psi_sqrt_segment_406539_411539)
          (psi_sqrt_segment_comp psi_sqrt_segment_411539_416539 psi_sqrt_segment_416539_421539))
        (psi_sqrt_segment_comp
          (psi_sqrt_segment_comp psi_sqrt_segment_421539_426539 psi_sqrt_segment_426539_431539)
          (psi_sqrt_segment_comp psi_sqrt_segment_431539_436539 psi_sqrt_segment_436539_441539)))
      (psi_sqrt_segment_comp
        (psi_sqrt_segment_comp
          (psi_sqrt_segment_comp psi_sqrt_segment_441539_446539 psi_sqrt_segment_446539_451539)
          (psi_sqrt_segment_comp psi_sqrt_segment_451539_456539 psi_sqrt_segment_456539_461539))
        (psi_sqrt_segment_comp
          (psi_sqrt_segment_comp psi_sqrt_segment_461539_466539 psi_sqrt_segment_466539_471539)
          (psi_sqrt_segment_comp psi_sqrt_segment_471539_476539 psi_sqrt_segment_476539_481539))))

end PseudoPrime.AnalyticNumberTheory.Arithmetic
