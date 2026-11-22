/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch641539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch646539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch651539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch656539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch661539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch666539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch671539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch676539

/-! # Composition of adjacent high batches -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

/-- Adjacent high batches give the joint estimates on [641539,681539). -/
theorem joined641539To681539 :
    Segment Valid highEstimate
      ⟨641539, 641335004472386096, 641339831537883740, 887461196452993, 887472396843589⟩
      ⟨681539, 681474710851515516, 681479826622517843, 914278741120503, 914290154891211⟩ := by
  have h1 := segment_comp batch641539 batch646539
  have h2 := segment_comp batch651539 batch656539
  have h3 := segment_comp batch661539 batch666539
  have h4 := segment_comp batch671539 batch676539
  have h5 := segment_comp h1 h2
  have h6 := segment_comp h3 h4
  have h7 := segment_comp h5 h6
  exact h7

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
