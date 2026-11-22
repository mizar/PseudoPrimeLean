/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch881539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch886539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch891539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch896539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch901539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch906539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch911539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch916539

/-! # Composition of adjacent high batches -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

/-- Adjacent high batches give the joint estimates on [881539,921539). -/
theorem joined881539To921539 :
    Segment Valid highEstimate
      ⟨881539, 881909430338492309, 881915694672363901, 1032522688658498, 1032535178279526⟩
      ⟨921539, 921671437706796767, 921677866978525237, 1057657255195228, 1057669947687839⟩ := by
  have h1 := segment_comp batch881539 batch886539
  have h2 := segment_comp batch891539 batch896539
  have h3 := segment_comp batch901539 batch906539
  have h4 := segment_comp batch911539 batch916539
  have h5 := segment_comp h1 h2
  have h6 := segment_comp h3 h4
  have h7 := segment_comp h5 h6
  exact h7

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
