/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch281539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch286539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch291539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch296539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch301539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch306539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch311539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch316539

/-! # Composition of adjacent high batches -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

/-- Adjacent high batches give the joint estimates on [281539,321539). -/
theorem joined281539To321539 :
    Segment Valid highEstimate
      ⟨281539, 281532440907291208, 281534577313136198, 600377131139129, 600384206880252⟩
      ⟨321539, 321593397510605728, 321595949965862868, 629835526100654, 629843334818269⟩ := by
  have h1 := segment_comp batch281539 batch286539
  have h2 := segment_comp batch291539 batch296539
  have h3 := segment_comp batch301539 batch306539
  have h4 := segment_comp batch311539 batch316539
  have h5 := segment_comp h1 h2
  have h6 := segment_comp h3 h4
  have h7 := segment_comp h5 h6
  exact h7

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
