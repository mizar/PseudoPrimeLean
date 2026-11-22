/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrtSegment
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound.ChebyshevSqrt561539To566539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound.ChebyshevSqrt566539To571539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound.ChebyshevSqrt571539To576539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound.ChebyshevSqrt576539To581539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound.ChebyshevSqrt581539To586539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound.ChebyshevSqrt586539To591539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound.ChebyshevSqrt591539To596539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound.ChebyshevSqrt596539To601539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound.ChebyshevSqrt601539To606539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound.ChebyshevSqrt606539To611539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound.ChebyshevSqrt611539To616539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound.ChebyshevSqrt616539To621539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound.ChebyshevSqrt621539To626539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound.ChebyshevSqrt626539To631539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound.ChebyshevSqrt631539To636539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound.ChebyshevSqrt636539To641539

/-! # Independent finite psi segment group 8 -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- Compose the checked intervals from 561539 to 641539; the source certificates
are consumed privately and this theorem contains no computational data. -/
theorem psi_sqrt_group08 :
    PsiSqrtSegment 1000000000000
      ⟨561539, 13238435671645, 13238764911035, 561513681950244697, 561529243242136321⟩
      ⟨641539, 13371624380388, 13371953810676, 641334726527444506, 641352262360531764⟩ := by
  exact
    (psi_sqrt_segment_comp
      (psi_sqrt_segment_comp
        (psi_sqrt_segment_comp
          (psi_sqrt_segment_comp psi_sqrt_segment_561539_566539 psi_sqrt_segment_566539_571539)
          (psi_sqrt_segment_comp psi_sqrt_segment_571539_576539 psi_sqrt_segment_576539_581539))
        (psi_sqrt_segment_comp
          (psi_sqrt_segment_comp psi_sqrt_segment_581539_586539 psi_sqrt_segment_586539_591539)
          (psi_sqrt_segment_comp psi_sqrt_segment_591539_596539 psi_sqrt_segment_596539_601539)))
      (psi_sqrt_segment_comp
        (psi_sqrt_segment_comp
          (psi_sqrt_segment_comp psi_sqrt_segment_601539_606539 psi_sqrt_segment_606539_611539)
          (psi_sqrt_segment_comp psi_sqrt_segment_611539_616539 psi_sqrt_segment_616539_621539))
        (psi_sqrt_segment_comp
          (psi_sqrt_segment_comp psi_sqrt_segment_621539_626539 psi_sqrt_segment_626539_631539)
          (psi_sqrt_segment_comp psi_sqrt_segment_631539_636539 psi_sqrt_segment_636539_641539))))

end PseudoPrime.AnalyticNumberTheory.Arithmetic
