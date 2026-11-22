/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighJoin3500To321539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighJoin321539To641539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighJoin641539To961539
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighJoin961539To1000000

/-! # Composition of adjacent high batches -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

/-- Adjacent high batches give the joint estimates on [3500,1000000). -/
theorem joined3500To1000000 :
    Segment Valid highEstimate
      ⟨3500, 3483879109733892, 3483920680466223, 74422413522765, 74422413522895⟩
      ⟨1000000, 999586518104918955, 999593238652839812, 1102422326452684, 1102435268224133⟩ := by
  have h1 := segment_comp joined3500To321539 joined321539To641539
  have h2 := segment_comp joined641539To961539 joined961539To1000000
  have h3 := segment_comp h1 h2
  exact h3

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
