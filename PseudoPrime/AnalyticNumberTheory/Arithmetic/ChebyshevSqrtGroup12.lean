/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrtSegment
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt881539To886539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt886539To891539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt891539To896539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt896539To901539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt901539To906539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt906539To911539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt911539To916539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt916539To921539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt921539To926539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt926539To931539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt931539To936539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt936539To941539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt941539To946539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt946539To951539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt951539To956539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt956539To961539

/-! # Independent finite psi segment group 12 -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- Compose the checked intervals from 881539 to 961539; the source certificates
are consumed privately and this theorem contains no computational data. -/
theorem psi_sqrt_group12 :
    PsiSqrtSegment 1000000000000
      ⟨881539, 13689423527043, 13689753409450, 881922840793111752, 881946231994344809⟩
      ⟨961539, 13776289369250, 13776619378846, 961392226244700784, 961417525694783338⟩ := by
  exact
    (psi_sqrt_segment_comp
      (psi_sqrt_segment_comp
        (psi_sqrt_segment_comp
          (psi_sqrt_segment_comp psi_sqrt_segment_881539_886539 psi_sqrt_segment_886539_891539)
          (psi_sqrt_segment_comp psi_sqrt_segment_891539_896539 psi_sqrt_segment_896539_901539))
        (psi_sqrt_segment_comp
          (psi_sqrt_segment_comp psi_sqrt_segment_901539_906539 psi_sqrt_segment_906539_911539)
          (psi_sqrt_segment_comp psi_sqrt_segment_911539_916539 psi_sqrt_segment_916539_921539)))
      (psi_sqrt_segment_comp
        (psi_sqrt_segment_comp
          (psi_sqrt_segment_comp psi_sqrt_segment_921539_926539 psi_sqrt_segment_926539_931539)
          (psi_sqrt_segment_comp psi_sqrt_segment_931539_936539 psi_sqrt_segment_936539_941539))
        (psi_sqrt_segment_comp
          (psi_sqrt_segment_comp psi_sqrt_segment_941539_946539 psi_sqrt_segment_946539_951539)
          (psi_sqrt_segment_comp psi_sqrt_segment_951539_956539 psi_sqrt_segment_956539_961539))))

end PseudoPrime.AnalyticNumberTheory.Arithmetic
