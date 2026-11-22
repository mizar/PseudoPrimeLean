/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch481539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch486539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch491539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch496539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch501539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch506539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch511539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch516539

/-! # Composition of adjacent high batches -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

/-- Adjacent high batches give the joint estimates on [481539,521539). -/
theorem joined481539To521539 :
    Segment Valid highEstimate
      ⟨481539, 481599705875598538, 481603188962441608, 784255016805820, 784264897886886⟩
      ⟨521539, 521708485598715597, 521712107609132688, 808318683224023, 808329077216397⟩ := by
  have h1 := segment_comp batch481539 batch486539
  have h2 := segment_comp batch491539 batch496539
  have h3 := segment_comp batch501539 batch506539
  have h4 := segment_comp batch511539 batch516539
  have h5 := segment_comp h1 h2
  have h6 := segment_comp h3 h4
  have h7 := segment_comp h5 h6
  exact h7

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
