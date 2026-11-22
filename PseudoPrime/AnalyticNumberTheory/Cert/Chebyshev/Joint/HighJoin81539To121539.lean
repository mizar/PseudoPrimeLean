/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch81539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch86539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch91539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch96539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch101539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch106539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch111539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch116539

/-! # Composition of adjacent high batches -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

/-- Adjacent high batches give the joint estimates on [81539,121539). -/
theorem joined81539To121539 :
    Segment Valid highEstimate
      ⟨81539, 81557656554439411, 81558397564588102, 340448479726655, 340452523982820⟩
      ⟨121539, 121519610010896173, 121520601328614569, 395201187251517, 395205913841299⟩ := by
  have h1 := segment_comp batch81539 batch86539
  have h2 := segment_comp batch91539 batch96539
  have h3 := segment_comp batch101539 batch106539
  have h4 := segment_comp batch111539 batch116539
  have h5 := segment_comp h1 h2
  have h6 := segment_comp h3 h4
  have h7 := segment_comp h5 h6
  exact h7

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
