/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrtSegment
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound.ChebyshevSqrtGroup01
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound.ChebyshevSqrtGroup02
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound.ChebyshevSqrtGroup03
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound.ChebyshevSqrtGroup04
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound.ChebyshevSqrtGroup05
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound.ChebyshevSqrtGroup06
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound.ChebyshevSqrtGroup07
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound.ChebyshevSqrtGroup08
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound.ChebyshevSqrtGroup09
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound.ChebyshevSqrtGroup10
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound.ChebyshevSqrtGroup11
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound.ChebyshevSqrtGroup12
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound.ChebyshevSqrtGroup13

/-! # Composition of independently checked psi intervals -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- The thirteen independent interval groups compose from 1539 to 1000001. -/
theorem psi_four_fifths_walk_segment :
    PsiSqrtSegment 1000000000000
      ⟨1539, 7338887595015, 7338892225039, 1530963112671469, 1531658116819066⟩
      ⟨1000001, 13815510503107, 13815840571449, 999586234305296029, 999612447035773994⟩ := by
  exact
    (psi_sqrt_segment_comp
      (psi_sqrt_segment_comp
        (psi_sqrt_segment_comp (psi_sqrt_segment_comp psi_sqrt_group01 psi_sqrt_group02)
          (psi_sqrt_segment_comp psi_sqrt_group03 psi_sqrt_group04))
        (psi_sqrt_segment_comp (psi_sqrt_segment_comp psi_sqrt_group05 psi_sqrt_group06)
          (psi_sqrt_segment_comp psi_sqrt_group07 psi_sqrt_group08)))
      (psi_sqrt_segment_comp
        (psi_sqrt_segment_comp (psi_sqrt_segment_comp psi_sqrt_group09 psi_sqrt_group10)
          (psi_sqrt_segment_comp psi_sqrt_group11 psi_sqrt_group12))
        psi_sqrt_group13))

end PseudoPrime.AnalyticNumberTheory.Arithmetic
