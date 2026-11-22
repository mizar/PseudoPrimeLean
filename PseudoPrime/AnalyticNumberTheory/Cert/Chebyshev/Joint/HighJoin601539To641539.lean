/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch601539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch606539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch611539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch616539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch621539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch626539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch631539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch636539

/-! # Composition of adjacent high batches -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

/-- Adjacent high batches give the joint estimates on [601539,641539). -/
theorem joined601539To641539 :
    Segment Valid highEstimate
      ⟨601539, 601650083532281086, 601654522595905655, 874112115045486, 874123170639620⟩
      ⟨641539, 641335004472386096, 641339831537883740, 887461196452993, 887472396843589⟩ := by
  have h1 := segment_comp batch601539 batch606539
  have h2 := segment_comp batch611539 batch616539
  have h3 := segment_comp batch621539 batch626539
  have h4 := segment_comp batch631539 batch636539
  have h5 := segment_comp h1 h2
  have h6 := segment_comp h3 h4
  have h7 := segment_comp h5 h6
  exact h7

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
