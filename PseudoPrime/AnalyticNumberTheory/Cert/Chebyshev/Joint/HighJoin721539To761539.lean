/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch721539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch726539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch731539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch736539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch741539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch746539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch751539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch756539

/-! # Composition of adjacent high batches -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

/-- Adjacent high batches give the joint estimates on [721539,761539). -/
theorem joined721539To761539 :
    Segment Valid highEstimate
      ⟨721539, 721508536774991476, 721513970640436545, 942304906054199, 942316637549039⟩
      ⟨761539, 761395293678725090, 761400941553885399, 969323284128657, 969335329903535⟩ := by
  have h1 := segment_comp batch721539 batch726539
  have h2 := segment_comp batch731539 batch736539
  have h3 := segment_comp batch741539 batch746539
  have h4 := segment_comp batch751539 batch756539
  have h5 := segment_comp h1 h2
  have h6 := segment_comp h3 h4
  have h7 := segment_comp h5 h6
  exact h7

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
