/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch161539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch166539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch171539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch176539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch181539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch186539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch191539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch196539

/-! # Composition of adjacent high batches -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

/-- Adjacent high batches give the joint estimates on [161539,201539). -/
theorem joined161539To201539 :
    Segment Valid highEstimate
      ⟨161539, 161579996956010881, 161581356023361584, 464465800923861, 464471490629316⟩
      ⟨201539, 201467683251723675, 201469340429682681, 507973543428502, 507979627855476⟩ := by
  have h1 := segment_comp batch161539 batch166539
  have h2 := segment_comp batch171539 batch176539
  have h3 := segment_comp batch181539 batch186539
  have h4 := segment_comp batch191539 batch196539
  have h5 := segment_comp h1 h2
  have h6 := segment_comp h3 h4
  have h7 := segment_comp h5 h6
  exact h7

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
