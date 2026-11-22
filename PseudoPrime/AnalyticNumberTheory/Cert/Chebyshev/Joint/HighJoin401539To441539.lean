/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch401539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch406539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch411539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch416539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch421539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch426539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch431539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch436539

/-! # Composition of adjacent high batches -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

/-- Adjacent high batches give the joint estimates on [401539,441539). -/
theorem joined401539To441539 :
    Segment Valid highEstimate
      ⟨401539, 401501442285022596, 401504570700224349, 719293395548567, 719302786537951⟩
      ⟨441539, 441586288667678169, 441589611114374059, 758160967129436, 758170675943213⟩ := by
  have h1 := segment_comp batch401539 batch406539
  have h2 := segment_comp batch411539 batch416539
  have h3 := segment_comp batch421539 batch426539
  have h4 := segment_comp batch431539 batch436539
  have h5 := segment_comp h1 h2
  have h6 := segment_comp h3 h4
  have h7 := segment_comp h5 h6
  exact h7

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
