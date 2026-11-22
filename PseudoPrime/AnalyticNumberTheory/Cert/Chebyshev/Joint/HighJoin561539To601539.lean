/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch561539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch566539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch571539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch576539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch581539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch586539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch591539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch596539

/-! # Composition of adjacent high batches -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

/-- Adjacent high batches give the joint estimates on [561539,601539). -/
theorem joined561539To601539 :
    Segment Valid highEstimate
      ⟨561539, 561513965587696661, 561517999202475834, 836512506291081, 836523164081411⟩
      ⟨601539, 601650083532281086, 601654522595905655, 874112115045486, 874123170639620⟩ := by
  have h1 := segment_comp batch561539 batch566539
  have h2 := segment_comp batch571539 batch576539
  have h3 := segment_comp batch581539 batch586539
  have h4 := segment_comp batch591539 batch596539
  have h5 := segment_comp h1 h2
  have h6 := segment_comp h3 h4
  have h7 := segment_comp h5 h6
  exact h7

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
