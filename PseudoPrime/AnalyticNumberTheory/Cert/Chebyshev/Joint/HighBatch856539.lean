/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 856539 to 861539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e856539 : Edge :=
  ⟨856539, 856500997878603721, 856507149722914125, 1018845896939750, 1018858338951882⟩

private def e861539 : Edge :=
  ⟨861539, 861460856494600496, 861467021221729155, 1018845896939750, 1018858338951882⟩

private def extra856539 : ℕ → ℕ
  | 856539 => 701
  | 857241 => 715
  | 857957 => 759
  | 858717 => 710
  | 859428 => 683
  | 860112 => 723
  | 860836 => 702
  | _ => 0

private theorem part856539 : Segment Valid highEstimate e856539 e861539 := by
  apply gcd_batch (by decide) (by decide) extra856539 7
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [856539,861539). -/
theorem batch856539 :
    Segment Valid highEstimate
      ⟨856539, 856500997878603721, 856507149722914125, 1018845896939750, 1018858338951882⟩
      ⟨861539, 861460856494600496, 861467021221729155, 1018845896939750, 1018858338951882⟩ := by
  exact part856539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
