/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch801539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch806539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch811539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch816539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch821539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch826539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch831539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch836539

/-! # Composition of adjacent high batches -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

/-- Adjacent high batches give the joint estimates on [801539,841539). -/
theorem joined801539To841539 :
    Segment Valid highEstimate
      ⟨801539, 801722201739233966, 801728096680372869, 996452017626611, 996464214691058⟩
      ⟨841539, 841613699477514666, 841619776629808475, 1012022610967268, 1012035023523210⟩ := by
  have h1 := segment_comp batch801539 batch806539
  have h2 := segment_comp batch811539 batch816539
  have h3 := segment_comp batch821539 batch826539
  have h4 := segment_comp batch831539 batch836539
  have h5 := segment_comp h1 h2
  have h6 := segment_comp h3 h4
  have h7 := segment_comp h5 h6
  exact h7

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
