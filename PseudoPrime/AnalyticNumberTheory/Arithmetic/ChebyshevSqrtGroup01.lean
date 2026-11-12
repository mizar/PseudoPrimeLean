/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrtSegment
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt1539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt6539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt11539To16539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt16539To21539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt21539To26539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt26539To31539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt31539To36539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt36539To41539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt41539To46539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt46539To51539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt51539To56539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt56539To61539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt61539To66539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt66539To71539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt71539To76539
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt76539To81539

/-! # Independent finite psi segment group 1 -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- Compose the checked intervals from 1539 to 81539; the source certificates
are consumed privately and this theorem contains no computational data. -/
theorem psi_sqrt_group01 :
    PsiSqrtSegment 1000000000000
      ⟨1539, 7338887595015, 7338892225039, 1530963112671469, 1531658116819066⟩
      ⟨81539, 11308836116126, 11309159633514, 81557361689696239, 81560391893266546⟩ := by
  exact
    (psi_sqrt_segment_comp
      (psi_sqrt_segment_comp
        (psi_sqrt_segment_comp
          (psi_sqrt_segment_comp psi_walk_1539_6539
            (fun hs =>
              ⟨psi_walk_11539_valid hs, fun x hx hy => psi_four_fifths_6539_11539 hs hx hy⟩))
          (psi_sqrt_segment_comp psi_sqrt_segment_11539_16539 psi_sqrt_segment_16539_21539))
        (psi_sqrt_segment_comp
          (psi_sqrt_segment_comp psi_sqrt_segment_21539_26539 psi_sqrt_segment_26539_31539)
          (psi_sqrt_segment_comp psi_sqrt_segment_31539_36539 psi_sqrt_segment_36539_41539)))
      (psi_sqrt_segment_comp
        (psi_sqrt_segment_comp
          (psi_sqrt_segment_comp psi_sqrt_segment_41539_46539 psi_sqrt_segment_46539_51539)
          (psi_sqrt_segment_comp psi_sqrt_segment_51539_56539 psi_sqrt_segment_56539_61539))
        (psi_sqrt_segment_comp
          (psi_sqrt_segment_comp psi_sqrt_segment_61539_66539 psi_sqrt_segment_66539_71539)
          (psi_sqrt_segment_comp psi_sqrt_segment_71539_76539 psi_sqrt_segment_76539_81539))))

end PseudoPrime.AnalyticNumberTheory.Arithmetic
