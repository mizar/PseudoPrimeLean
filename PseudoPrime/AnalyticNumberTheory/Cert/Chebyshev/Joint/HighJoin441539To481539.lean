/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch441539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch446539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch451539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch456539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch461539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch466539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch471539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch476539

/-! # Composition of adjacent high batches -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

/-- Adjacent high batches give the joint estimates on [441539,481539). -/
theorem joined441539To481539 :
    Segment Valid highEstimate
      ⟨441539, 441586288667678169, 441589611114374059, 758160967129436, 758170675943213⟩
      ⟨481539, 481599705875598538, 481603188962441608, 784255016805820, 784264897886886⟩ := by
  have h1 := segment_comp batch441539 batch446539
  have h2 := segment_comp batch451539 batch456539
  have h3 := segment_comp batch461539 batch466539
  have h4 := segment_comp batch471539 batch476539
  have h5 := segment_comp h1 h2
  have h6 := segment_comp h3 h4
  have h7 := segment_comp h5 h6
  exact h7

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
