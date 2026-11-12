/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrtSegment
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt481539To486539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt486539To491539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt491539To496539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt496539To501539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt501539To506539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt506539To511539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt511539To516539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt516539To521539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt521539To526539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt526539To531539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt531539To536539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt536539To541539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt541539To546539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt546539To551539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt551539To556539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt556539To561539

/-! # Independent finite psi segment group 7 -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- Compose the checked intervals from 481539 to 561539; the source certificates
are consumed privately and this theorem contains no computational data. -/
theorem psi_sqrt_group07 :
    PsiSqrtSegment 1000000000000
      ⟨481539, 13084741707750, 13085070719213, 481599420075311906, 481612984332317400⟩
      ⟨561539, 13238435671645, 13238764911035, 561513681950244697, 561529243242136321⟩ := by
  exact
    (psi_sqrt_segment_comp
      (psi_sqrt_segment_comp
        (psi_sqrt_segment_comp
          (psi_sqrt_segment_comp psi_sqrt_segment_481539_486539 psi_sqrt_segment_486539_491539)
          (psi_sqrt_segment_comp psi_sqrt_segment_491539_496539 psi_sqrt_segment_496539_501539))
        (psi_sqrt_segment_comp
          (psi_sqrt_segment_comp psi_sqrt_segment_501539_506539 psi_sqrt_segment_506539_511539)
          (psi_sqrt_segment_comp psi_sqrt_segment_511539_516539 psi_sqrt_segment_516539_521539)))
      (psi_sqrt_segment_comp
        (psi_sqrt_segment_comp
          (psi_sqrt_segment_comp psi_sqrt_segment_521539_526539 psi_sqrt_segment_526539_531539)
          (psi_sqrt_segment_comp psi_sqrt_segment_531539_536539 psi_sqrt_segment_536539_541539))
        (psi_sqrt_segment_comp
          (psi_sqrt_segment_comp psi_sqrt_segment_541539_546539 psi_sqrt_segment_546539_551539)
          (psi_sqrt_segment_comp psi_sqrt_segment_551539_556539 psi_sqrt_segment_556539_561539))))

end PseudoPrime.AnalyticNumberTheory.Arithmetic
