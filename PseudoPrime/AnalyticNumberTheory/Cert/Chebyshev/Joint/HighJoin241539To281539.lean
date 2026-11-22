/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch241539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch246539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch251539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch256539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch261539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch266539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch271539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch276539

/-! # Composition of adjacent high batches -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

/-- Adjacent high batches give the joint estimates on [241539,281539). -/
theorem joined241539To281539 :
    Segment Valid highEstimate
      ⟨241539, 241459179626994363, 241461027353903130, 565367520318279, 565374043686911⟩
      ⟨281539, 281532440907291208, 281534577313136198, 600377131139129, 600384206880252⟩ := by
  have h1 := segment_comp batch241539 batch246539
  have h2 := segment_comp batch251539 batch256539
  have h3 := segment_comp batch261539 batch266539
  have h4 := segment_comp batch271539 batch276539
  have h5 := segment_comp h1 h2
  have h6 := segment_comp h3 h4
  have h7 := segment_comp h5 h6
  exact h7

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
