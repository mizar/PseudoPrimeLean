/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch201539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch206539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch211539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch216539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch221539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch226539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch231539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch236539

/-! # Composition of adjacent high batches -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

/-- Adjacent high batches give the joint estimates on [201539,241539). -/
theorem joined201539To241539 :
    Segment Valid highEstimate
      ⟨201539, 201467683251723675, 201469340429682681, 507973543428502, 507979627855476⟩
      ⟨241539, 241459179626994363, 241461027353903130, 565367520318279, 565374043686911⟩ := by
  have h1 := segment_comp batch201539 batch206539
  have h2 := segment_comp batch211539 batch216539
  have h3 := segment_comp batch221539 batch226539
  have h4 := segment_comp batch231539 batch236539
  have h5 := segment_comp h1 h2
  have h6 := segment_comp h3 h4
  have h7 := segment_comp h5 h6
  exact h7

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
