/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighJoin3500To41539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighJoin41539To81539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighJoin81539To121539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighJoin121539To161539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighJoin161539To201539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighJoin201539To241539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighJoin241539To281539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighJoin281539To321539

/-! # Composition of adjacent high batches -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

/-- Adjacent high batches give the joint estimates on [3500,321539). -/
theorem joined3500To321539 :
    Segment Valid highEstimate
      ⟨3500, 3483879109733892, 3483920680466223, 74422413522765, 74422413522895⟩
      ⟨321539, 321593397510605728, 321595949965862868, 629835526100654, 629843334818269⟩ := by
  have h1 := segment_comp joined3500To41539 joined41539To81539
  have h2 := segment_comp joined81539To121539 joined121539To161539
  have h3 := segment_comp joined161539To201539 joined201539To241539
  have h4 := segment_comp joined241539To281539 joined281539To321539
  have h5 := segment_comp h1 h2
  have h6 := segment_comp h3 h4
  have h7 := segment_comp h5 h6
  exact h7

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
