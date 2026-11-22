/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrtSegment
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound.ChebyshevSqrt161539To166539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound.ChebyshevSqrt166539To171539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound.ChebyshevSqrt171539To176539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound.ChebyshevSqrt176539To181539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound.ChebyshevSqrt181539To186539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound.ChebyshevSqrt186539To191539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound.ChebyshevSqrt191539To196539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound.ChebyshevSqrt196539To201539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound.ChebyshevSqrt201539To206539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound.ChebyshevSqrt206539To211539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound.ChebyshevSqrt211539To216539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound.ChebyshevSqrt216539To221539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound.ChebyshevSqrt221539To226539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound.ChebyshevSqrt226539To231539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound.ChebyshevSqrt231539To236539
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound.ChebyshevSqrt236539To241539

/-! # Independent finite psi segment group 3 -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- Compose the checked intervals from 161539 to 241539; the source certificates
are consumed privately and this theorem contains no computational data. -/
theorem psi_sqrt_group03 :
    PsiSqrtSegment 1000000000000
      ⟨161539, 11992501242275, 11992827876729, 161579705184422469, 161584960690716936⟩
      ⟨241539, 12394785553519, 12395113293239, 241458888585524096, 241466283392081990⟩ := by
  exact
    (psi_sqrt_segment_comp
      (psi_sqrt_segment_comp
        (psi_sqrt_segment_comp
          (psi_sqrt_segment_comp psi_sqrt_segment_161539_166539 psi_sqrt_segment_166539_171539)
          (psi_sqrt_segment_comp psi_sqrt_segment_171539_176539 psi_sqrt_segment_176539_181539))
        (psi_sqrt_segment_comp
          (psi_sqrt_segment_comp psi_sqrt_segment_181539_186539 psi_sqrt_segment_186539_191539)
          (psi_sqrt_segment_comp psi_sqrt_segment_191539_196539 psi_sqrt_segment_196539_201539)))
      (psi_sqrt_segment_comp
        (psi_sqrt_segment_comp
          (psi_sqrt_segment_comp psi_sqrt_segment_201539_206539 psi_sqrt_segment_206539_211539)
          (psi_sqrt_segment_comp psi_sqrt_segment_211539_216539 psi_sqrt_segment_216539_221539))
        (psi_sqrt_segment_comp
          (psi_sqrt_segment_comp psi_sqrt_segment_221539_226539 psi_sqrt_segment_226539_231539)
          (psi_sqrt_segment_comp psi_sqrt_segment_231539_236539 psi_sqrt_segment_236539_241539))))

end PseudoPrime.AnalyticNumberTheory.Arithmetic
