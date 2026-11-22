/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch361539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch366539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch371539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch376539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch381539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch386539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch391539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch396539

/-! # Composition of adjacent high batches -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

/-- Adjacent high batches give the joint estimates on [361539,401539). -/
theorem joined361539To401539 :
    Segment Valid highEstimate
      ⟨361539, 361621228998278365, 361624100837074789, 678701384824462, 678709988403382⟩
      ⟨401539, 401501442285022596, 401504570700224349, 719293395548567, 719302786537951⟩ := by
  have h1 := segment_comp batch361539 batch366539
  have h2 := segment_comp batch371539 batch376539
  have h3 := segment_comp batch381539 batch386539
  have h4 := segment_comp batch391539 batch396539
  have h5 := segment_comp h1 h2
  have h6 := segment_comp h3 h4
  have h7 := segment_comp h5 h6
  exact h7

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
