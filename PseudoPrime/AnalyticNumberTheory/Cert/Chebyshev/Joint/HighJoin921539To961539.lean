/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch921539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch926539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch931539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch936539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch941539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch946539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch951539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch956539

/-! # Composition of adjacent high batches -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

/-- Adjacent high batches give the joint estimates on [921539,961539). -/
theorem joined921539To961539 :
    Segment Valid highEstimate
      ⟨921539, 921671437706796767, 921677866978525237, 1057657255195228, 1057669947687839⟩
      ⟨961539, 961392508433358735, 961399078287689346, 1081728253389386, 1081741038637830⟩ := by
  have h1 := segment_comp batch921539 batch926539
  have h2 := segment_comp batch931539 batch936539
  have h3 := segment_comp batch941539 batch946539
  have h4 := segment_comp batch951539 batch956539
  have h5 := segment_comp h1 h2
  have h6 := segment_comp h3 h4
  have h7 := segment_comp h5 h6
  exact h7

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
