/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch761539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch766539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch771539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch776539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch781539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch786539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch791539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch796539

/-! # Composition of adjacent high batches -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

/-- Adjacent high batches give the joint estimates on [761539,801539). -/
theorem joined761539To801539 :
    Segment Valid highEstimate
      ⟨761539, 761395293678725090, 761400941553885399, 969323284128657, 969335329903535⟩
      ⟨801539, 801722201739233966, 801728096680372869, 996452017626611, 996464214691058⟩ := by
  have h1 := segment_comp batch761539 batch766539
  have h2 := segment_comp batch771539 batch776539
  have h3 := segment_comp batch781539 batch786539
  have h4 := segment_comp batch791539 batch796539
  have h5 := segment_comp h1 h2
  have h6 := segment_comp h3 h4
  have h7 := segment_comp h5 h6
  exact h7

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
