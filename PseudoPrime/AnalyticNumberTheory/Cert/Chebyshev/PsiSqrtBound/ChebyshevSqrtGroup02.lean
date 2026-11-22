/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrtSegment
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound.ChebyshevSqrt81539To86539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound.ChebyshevSqrt86539To91539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound.ChebyshevSqrt91539To96539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound.ChebyshevSqrt96539To101539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound.ChebyshevSqrt101539To106539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound.ChebyshevSqrt106539To111539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound.ChebyshevSqrt111539To116539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound.ChebyshevSqrt116539To121539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound.ChebyshevSqrt121539To126539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound.ChebyshevSqrt126539To131539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound.ChebyshevSqrt131539To136539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound.ChebyshevSqrt136539To141539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound.ChebyshevSqrt141539To146539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound.ChebyshevSqrt146539To151539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound.ChebyshevSqrt151539To156539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound.ChebyshevSqrt156539To161539

/-! # Independent finite psi segment group 2 -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- Compose the checked intervals from 81539 to 161539; the source certificates
are consumed privately and this theorem contains no computational data. -/
theorem psi_sqrt_group02 :
    PsiSqrtSegment 1000000000000
      ⟨81539, 11308836116126, 11309159633514, 81557361689696239, 81560391893266546⟩
      ⟨161539, 11992501242275, 11992827876729, 161579705184422469, 161584960690716936⟩ := by
  exact
    (psi_sqrt_segment_comp
      (psi_sqrt_segment_comp
        (psi_sqrt_segment_comp
          (psi_sqrt_segment_comp psi_sqrt_segment_81539_86539 psi_sqrt_segment_86539_91539)
          (psi_sqrt_segment_comp psi_sqrt_segment_91539_96539 psi_sqrt_segment_96539_101539))
        (psi_sqrt_segment_comp
          (psi_sqrt_segment_comp psi_sqrt_segment_101539_106539 psi_sqrt_segment_106539_111539)
          (psi_sqrt_segment_comp psi_sqrt_segment_111539_116539 psi_sqrt_segment_116539_121539)))
      (psi_sqrt_segment_comp
        (psi_sqrt_segment_comp
          (psi_sqrt_segment_comp psi_sqrt_segment_121539_126539 psi_sqrt_segment_126539_131539)
          (psi_sqrt_segment_comp psi_sqrt_segment_131539_136539 psi_sqrt_segment_136539_141539))
        (psi_sqrt_segment_comp
          (psi_sqrt_segment_comp psi_sqrt_segment_141539_146539 psi_sqrt_segment_146539_151539)
          (psi_sqrt_segment_comp psi_sqrt_segment_151539_156539 psi_sqrt_segment_156539_161539))))

end PseudoPrime.AnalyticNumberTheory.Arithmetic
