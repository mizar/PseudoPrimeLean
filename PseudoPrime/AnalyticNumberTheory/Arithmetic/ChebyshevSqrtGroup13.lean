/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrtSegment
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt961539To966539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt966539To971539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt971539To976539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt976539To981539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt981539To986539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt986539To991539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt991539To996539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt996539To1000001

/-! # Independent finite psi segment group 13 -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- Compose the checked intervals from 961539 to 1000001; the source certificates
are consumed privately and this theorem contains no computational data. -/
theorem psi_sqrt_group13 :
    PsiSqrtSegment 1000000000000
      ⟨961539, 13776289369250, 13776619378846, 961392226244700784, 961417525694783338⟩
      ⟨1000001, 13815510503107, 13815840571449, 999586234305296029, 999612447035773994⟩ := by
  exact
    (psi_sqrt_segment_comp
      (psi_sqrt_segment_comp
        (psi_sqrt_segment_comp psi_sqrt_segment_961539_966539 psi_sqrt_segment_966539_971539)
        (psi_sqrt_segment_comp psi_sqrt_segment_971539_976539 psi_sqrt_segment_976539_981539))
      (psi_sqrt_segment_comp
        (psi_sqrt_segment_comp psi_sqrt_segment_981539_986539 psi_sqrt_segment_986539_991539)
        (psi_sqrt_segment_comp psi_sqrt_segment_991539_996539 psi_sqrt_segment_996539_1000001)))

end PseudoPrime.AnalyticNumberTheory.Arithmetic
