/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrtSegment
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt801539To806539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt806539To811539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt811539To816539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt816539To821539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt821539To826539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt826539To831539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt831539To836539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt836539To841539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt841539To846539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt846539To851539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt851539To856539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt856539To861539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt861539To866539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt866539To871539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt871539To876539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt876539To881539

/-! # Independent finite psi segment group 11 -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- Compose the checked intervals from 801539 to 881539; the source certificates
are consumed privately and this theorem contains no computational data. -/
theorem psi_sqrt_group11 :
    PsiSqrtSegment 1000000000000
      ⟨801539, 13594287952934, 13594617698852, 801735519267393580, 801756972677928850⟩
      ⟨881539, 13689423527043, 13689753409450, 881922840793111752, 881946231994344809⟩ := by
  exact
    (psi_sqrt_segment_comp
      (psi_sqrt_segment_comp
        (psi_sqrt_segment_comp
          (psi_sqrt_segment_comp psi_sqrt_segment_801539_806539 psi_sqrt_segment_806539_811539)
          (psi_sqrt_segment_comp psi_sqrt_segment_811539_816539 psi_sqrt_segment_816539_821539))
        (psi_sqrt_segment_comp
          (psi_sqrt_segment_comp psi_sqrt_segment_821539_826539 psi_sqrt_segment_826539_831539)
          (psi_sqrt_segment_comp psi_sqrt_segment_831539_836539 psi_sqrt_segment_836539_841539)))
      (psi_sqrt_segment_comp
        (psi_sqrt_segment_comp
          (psi_sqrt_segment_comp psi_sqrt_segment_841539_846539 psi_sqrt_segment_846539_851539)
          (psi_sqrt_segment_comp psi_sqrt_segment_851539_856539 psi_sqrt_segment_856539_861539))
        (psi_sqrt_segment_comp
          (psi_sqrt_segment_comp psi_sqrt_segment_861539_866539 psi_sqrt_segment_866539_871539)
          (psi_sqrt_segment_comp psi_sqrt_segment_871539_876539 psi_sqrt_segment_876539_881539))))

end PseudoPrime.AnalyticNumberTheory.Arithmetic
