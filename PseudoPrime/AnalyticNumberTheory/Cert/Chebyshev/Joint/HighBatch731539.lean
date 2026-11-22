/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 731539 to 736539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e731539 : Edge :=
  ⟨731539, 731529303067427572, 731534765250192739, 949053665533654, 949065414411248⟩

private def e736539 : Edge :=
  ⟨736539, 736654950214771859, 736660476226230268, 955807103056896, 955818908254589⟩

private def extra731539 : ℕ → ℕ
  | 731539 => 641
  | 732181 => 651
  | 732833 => 625
  | 733459 => 683
  | 734143 => 663
  | 734807 => 565
  | 735373 => 579
  | 735953 => 517
  | 736471 => 67
  | _ => 0

private theorem part731539 : Segment Valid highEstimate e731539 e736539 := by
  apply gcd_batch (by decide) (by decide) extra731539 9
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [731539,736539). -/
theorem batch731539 :
    Segment Valid highEstimate
      ⟨731539, 731529303067427572, 731534765250192739, 949053665533654, 949065414411248⟩
      ⟨736539, 736654950214771859, 736660476226230268, 955807103056896, 955818908254589⟩ := by
  exact part731539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
