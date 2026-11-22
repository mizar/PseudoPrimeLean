/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 851539 to 856539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e851539 : Edge :=
  ⟨851539, 851611514203447833, 851617658626068577, 1018845896939750, 1018858338951882⟩

private def e856539 : Edge :=
  ⟨856539, 856500997878603721, 856507149722914125, 1018845896939750, 1018858338951882⟩

private def extra851539 : ℕ → ℕ
  | 851539 => 671
  | 852211 => 669
  | 852881 => 805
  | 853687 => 670
  | 854358 => 709
  | 855068 => 655
  | 855724 => 655
  | 856380 => 158
  | _ => 0

private theorem part851539 : Segment Valid highEstimate e851539 e856539 := by
  apply gcd_batch (by decide) (by decide) extra851539 8
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [851539,856539). -/
theorem batch851539 :
    Segment Valid highEstimate
      ⟨851539, 851611514203447833, 851617658626068577, 1018845896939750, 1018858338951882⟩
      ⟨856539, 856500997878603721, 856507149722914125, 1018845896939750, 1018858338951882⟩ := by
  exact part851539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
