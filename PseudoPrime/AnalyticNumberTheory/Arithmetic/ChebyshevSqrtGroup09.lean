/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrtSegment
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt641539To646539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt646539To651539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt651539To656539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt656539To661539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt661539To666539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt666539To671539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt671539To676539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt676539To681539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt681539To686539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt686539To691539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt691539To696539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt696539To701539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt701539To706539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt706539To711539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt711539To716539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt716539To721539

/-! # Independent finite psi segment group 9 -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- Compose the checked intervals from 641539 to 721539; the source certificates
are consumed privately and this theorem contains no computational data. -/
theorem psi_sqrt_group09 :
    PsiSqrtSegment 1000000000000
      ⟨641539, 13371624380388, 13371953810676, 641334726527444506, 641352262360531764⟩
      ⟨721539, 13489140794105, 13489470390876, 721508260724497441, 721527762304433959⟩ := by
  exact
    (psi_sqrt_segment_comp
      (psi_sqrt_segment_comp
        (psi_sqrt_segment_comp
          (psi_sqrt_segment_comp psi_sqrt_segment_641539_646539 psi_sqrt_segment_646539_651539)
          (psi_sqrt_segment_comp psi_sqrt_segment_651539_656539 psi_sqrt_segment_656539_661539))
        (psi_sqrt_segment_comp
          (psi_sqrt_segment_comp psi_sqrt_segment_661539_666539 psi_sqrt_segment_666539_671539)
          (psi_sqrt_segment_comp psi_sqrt_segment_671539_676539 psi_sqrt_segment_676539_681539)))
      (psi_sqrt_segment_comp
        (psi_sqrt_segment_comp
          (psi_sqrt_segment_comp psi_sqrt_segment_681539_686539 psi_sqrt_segment_686539_691539)
          (psi_sqrt_segment_comp psi_sqrt_segment_691539_696539 psi_sqrt_segment_696539_701539))
        (psi_sqrt_segment_comp
          (psi_sqrt_segment_comp psi_sqrt_segment_701539_706539 psi_sqrt_segment_706539_711539)
          (psi_sqrt_segment_comp psi_sqrt_segment_711539_716539 psi_sqrt_segment_716539_721539))))

end PseudoPrime.AnalyticNumberTheory.Arithmetic
