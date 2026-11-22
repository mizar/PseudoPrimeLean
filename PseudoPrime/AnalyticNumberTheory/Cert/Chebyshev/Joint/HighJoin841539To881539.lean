/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch841539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch846539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch851539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch856539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch861539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch866539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch871539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch876539

/-! # Composition of adjacent high batches -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

/-- Adjacent high batches give the joint estimates on [841539,881539). -/
theorem joined841539To881539 :
    Segment Valid highEstimate
      ⟨841539, 841613699477514666, 841619776629808475, 1012022610967268, 1012035023523210⟩
      ⟨881539, 881909430338492309, 881915694672363901, 1032522688658498, 1032535178279526⟩ := by
  have h1 := segment_comp batch841539 batch846539
  have h2 := segment_comp batch851539 batch856539
  have h3 := segment_comp batch861539 batch866539
  have h4 := segment_comp batch871539 batch876539
  have h5 := segment_comp h1 h2
  have h6 := segment_comp h3 h4
  have h7 := segment_comp h5 h6
  exact h7

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
