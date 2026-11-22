/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighJoin641539To681539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighJoin681539To721539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighJoin721539To761539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighJoin761539To801539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighJoin801539To841539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighJoin841539To881539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighJoin881539To921539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighJoin921539To961539

/-! # Composition of adjacent high batches -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

/-- Adjacent high batches give the joint estimates on [641539,961539). -/
theorem joined641539To961539 :
    Segment Valid highEstimate
      ⟨641539, 641335004472386096, 641339831537883740, 887461196452993, 887472396843589⟩
      ⟨961539, 961392508433358735, 961399078287689346, 1081728253389386, 1081741038637830⟩ := by
  have h1 := segment_comp joined641539To681539 joined681539To721539
  have h2 := segment_comp joined721539To761539 joined761539To801539
  have h3 := segment_comp joined801539To841539 joined841539To881539
  have h4 := segment_comp joined881539To921539 joined921539To961539
  have h5 := segment_comp h1 h2
  have h6 := segment_comp h3 h4
  have h7 := segment_comp h5 h6
  exact h7

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
