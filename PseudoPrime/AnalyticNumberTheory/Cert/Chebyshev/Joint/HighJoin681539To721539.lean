/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch681539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch686539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch691539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch696539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch701539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch706539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch711539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch716539

/-! # Composition of adjacent high batches -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

/-- Adjacent high batches give the joint estimates on [681539,721539). -/
theorem joined681539To721539 :
    Segment Valid highEstimate
      ⟨681539, 681474710851515516, 681479826622517843, 914278741120503, 914290154891211⟩
      ⟨721539, 721508536774991476, 721513970640436545, 942304906054199, 942316637549039⟩ := by
  have h1 := segment_comp batch681539 batch686539
  have h2 := segment_comp batch691539 batch696539
  have h3 := segment_comp batch701539 batch706539
  have h4 := segment_comp batch711539 batch716539
  have h5 := segment_comp h1 h2
  have h6 := segment_comp h3 h4
  have h7 := segment_comp h5 h6
  exact h7

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
