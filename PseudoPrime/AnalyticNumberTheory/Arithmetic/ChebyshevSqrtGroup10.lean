/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrtSegment
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt721539To726539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt726539To731539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt731539To736539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt736539To741539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt741539To746539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt746539To751539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt751539To756539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt756539To761539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt761539To766539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt766539To771539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt771539To776539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt776539To781539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt781539To786539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt786539To791539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt791539To796539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt796539To801539

/-! # Independent finite psi segment group 10 -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- Compose the checked intervals from 721539 to 801539; the source certificates
are consumed privately and this theorem contains no computational data. -/
theorem psi_sqrt_group10 :
    PsiSqrtSegment 1000000000000
      ⟨721539, 13489140794105, 13489470390876, 721508260724497441, 721527762304433959⟩
      ⟨801539, 13594287952934, 13594617698852, 801735519267393580, 801756972677928850⟩ := by
  exact
    (psi_sqrt_segment_comp
      (psi_sqrt_segment_comp
        (psi_sqrt_segment_comp
          (psi_sqrt_segment_comp psi_sqrt_segment_721539_726539 psi_sqrt_segment_726539_731539)
          (psi_sqrt_segment_comp psi_sqrt_segment_731539_736539 psi_sqrt_segment_736539_741539))
        (psi_sqrt_segment_comp
          (psi_sqrt_segment_comp psi_sqrt_segment_741539_746539 psi_sqrt_segment_746539_751539)
          (psi_sqrt_segment_comp psi_sqrt_segment_751539_756539 psi_sqrt_segment_756539_761539)))
      (psi_sqrt_segment_comp
        (psi_sqrt_segment_comp
          (psi_sqrt_segment_comp psi_sqrt_segment_761539_766539 psi_sqrt_segment_766539_771539)
          (psi_sqrt_segment_comp psi_sqrt_segment_771539_776539 psi_sqrt_segment_776539_781539))
        (psi_sqrt_segment_comp
          (psi_sqrt_segment_comp psi_sqrt_segment_781539_786539 psi_sqrt_segment_786539_791539)
          (psi_sqrt_segment_comp psi_sqrt_segment_791539_796539 psi_sqrt_segment_796539_801539))))

end PseudoPrime.AnalyticNumberTheory.Arithmetic
