/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch121539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch126539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch131539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch136539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch141539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch146539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch151539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch156539

/-! # Composition of adjacent high batches -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

/-- Adjacent high batches give the joint estimates on [121539,161539). -/
theorem joined121539To161539 :
    Segment Valid highEstimate
      ⟨121539, 121519610010896173, 121520601328614569, 395201187251517, 395205913841299⟩
      ⟨161539, 161579996956010881, 161581356023361584, 464465800923861, 464471490629316⟩ := by
  have h1 := segment_comp batch121539 batch126539
  have h2 := segment_comp batch131539 batch136539
  have h3 := segment_comp batch141539 batch146539
  have h4 := segment_comp batch151539 batch156539
  have h5 := segment_comp h1 h2
  have h6 := segment_comp h3 h4
  have h7 := segment_comp h5 h6
  exact h7

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
