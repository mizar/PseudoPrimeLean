/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighJoin321539To361539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighJoin361539To401539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighJoin401539To441539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighJoin441539To481539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighJoin481539To521539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighJoin521539To561539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighJoin561539To601539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighJoin601539To641539

/-! # Composition of adjacent high batches -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

/-- Adjacent high batches give the joint estimates on [321539,641539). -/
theorem joined321539To641539 :
    Segment Valid highEstimate
      ⟨321539, 321593397510605728, 321595949965862868, 629835526100654, 629843334818269⟩
      ⟨641539, 641335004472386096, 641339831537883740, 887461196452993, 887472396843589⟩ := by
  have h1 := segment_comp joined321539To361539 joined361539To401539
  have h2 := segment_comp joined401539To441539 joined441539To481539
  have h3 := segment_comp joined481539To521539 joined521539To561539
  have h4 := segment_comp joined561539To601539 joined601539To641539
  have h5 := segment_comp h1 h2
  have h6 := segment_comp h3 h4
  have h7 := segment_comp h5 h6
  exact h7

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
