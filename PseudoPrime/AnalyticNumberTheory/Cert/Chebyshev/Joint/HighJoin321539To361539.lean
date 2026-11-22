/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch321539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch326539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch331539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch336539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch341539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch346539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch351539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch356539

/-! # Composition of adjacent high batches -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

/-- Adjacent high batches give the joint estimates on [321539,361539). -/
theorem joined321539To361539 :
    Segment Valid highEstimate
      ⟨321539, 321593397510605728, 321595949965862868, 629835526100654, 629843334818269⟩
      ⟨361539, 361621228998278365, 361624100837074789, 678701384824462, 678709988403382⟩ := by
  have h1 := segment_comp batch321539 batch326539
  have h2 := segment_comp batch331539 batch336539
  have h3 := segment_comp batch341539 batch346539
  have h4 := segment_comp batch351539 batch356539
  have h5 := segment_comp h1 h2
  have h6 := segment_comp h3 h4
  have h7 := segment_comp h5 h6
  exact h7

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
