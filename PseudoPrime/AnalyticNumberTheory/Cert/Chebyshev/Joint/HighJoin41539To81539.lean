/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch41539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch46539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch51539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch56539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch61539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch66539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch71539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch76539

/-! # Composition of adjacent high batches -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

/-- Adjacent high batches give the joint estimates on [41539,81539). -/
theorem joined41539To81539 :
    Segment Valid highEstimate
      ⟨41539, 41499131825914016, 41499532330518635, 243180280503640, 243182711459752⟩
      ⟨81539, 81557656554439411, 81558397564588102, 340448479726655, 340452523982820⟩ := by
  have h1 := segment_comp batch41539 batch46539
  have h2 := segment_comp batch51539 batch56539
  have h3 := segment_comp batch61539 batch66539
  have h4 := segment_comp batch71539 batch76539
  have h5 := segment_comp h1 h2
  have h6 := segment_comp h3 h4
  have h7 := segment_comp h5 h6
  exact h7

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
