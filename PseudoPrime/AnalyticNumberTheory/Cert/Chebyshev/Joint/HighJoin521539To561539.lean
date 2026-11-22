/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch521539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch526539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch531539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch536539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch541539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch546539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch551539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch556539

/-! # Composition of adjacent high batches -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

/-- Adjacent high batches give the joint estimates on [521539,561539). -/
theorem joined521539To561539 :
    Segment Valid highEstimate
      ⟨521539, 521708485598715597, 521712107609132688, 808318683224023, 808329077216397⟩
      ⟨561539, 561513965587696661, 561517999202475834, 836512506291081, 836523164081411⟩ := by
  have h1 := segment_comp batch521539 batch526539
  have h2 := segment_comp batch531539 batch536539
  have h3 := segment_comp batch541539 batch546539
  have h4 := segment_comp batch551539 batch556539
  have h5 := segment_comp h1 h2
  have h6 := segment_comp h3 h4
  have h7 := segment_comp h5 h6
  exact h7

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
