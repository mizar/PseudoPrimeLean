/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch961539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch966539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch971539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch976539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch981539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch986539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch991539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch996539

/-! # Composition of adjacent high batches -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

/-- Adjacent high batches give the joint estimates on [961539,1000000). -/
theorem joined961539To1000000 :
    Segment Valid highEstimate
      ⟨961539, 961392508433358735, 961399078287689346, 1081728253389386, 1081741038637830⟩
      ⟨1000000, 999586518104918955, 999593238652839812, 1102422326452684, 1102435268224133⟩ := by
  have h1 := segment_comp batch961539 batch966539
  have h2 := segment_comp batch971539 batch976539
  have h3 := segment_comp batch981539 batch986539
  have h4 := segment_comp batch991539 batch996539
  have h5 := segment_comp h1 h2
  have h6 := segment_comp h3 h4
  have h7 := segment_comp h5 h6
  exact h7

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
