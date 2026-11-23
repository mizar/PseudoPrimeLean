/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaGap7689341184
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaGap7721341184
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaGap7753341184
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaGap7785341184
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaGap7817341184
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaGap7849341184
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaGap7881341184
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaGap7886980184

/-! # Assembly of the finite gap estimates -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

/-- Combine the independent certificates across the full finite gap. -/
theorem theta_gap_7886980184 :
    ThetaLowerSegment 7657341184 7886980184 (382790423425787 / 50000)
      (788544761326621 / 100000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join (ThetaLowerSegment.join gap_window_7689341184 gap_window_7721341184)
        (ThetaLowerSegment.join gap_window_7753341184 gap_window_7785341184))
      (ThetaLowerSegment.join (ThetaLowerSegment.join gap_window_7817341184 gap_window_7849341184)
        (ThetaLowerSegment.join gap_window_7881341184 gap_window_7886980184)))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
