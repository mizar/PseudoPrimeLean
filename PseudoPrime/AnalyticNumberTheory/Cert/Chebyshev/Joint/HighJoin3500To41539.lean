/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch3500
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch6539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch11539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch16539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch21539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch26539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch31539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch36539

/-! # Composition of adjacent high batches -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

/-- Adjacent high batches give the joint estimates on [3500,41539). -/
theorem joined3500To41539 :
    Segment Valid highEstimate
      ⟨3500, 3483879109733892, 3483920680466223, 74422413522765, 74422413522895⟩
      ⟨41539, 41499131825914016, 41499532330518635, 243180280503640, 243182711459752⟩ := by
  have h1 := segment_comp batch3500 batch6539
  have h2 := segment_comp batch11539 batch16539
  have h3 := segment_comp batch21539 batch26539
  have h4 := segment_comp batch31539 batch36539
  have h5 := segment_comp h1 h2
  have h6 := segment_comp h3 h4
  have h7 := segment_comp h5 h6
  exact h7

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
