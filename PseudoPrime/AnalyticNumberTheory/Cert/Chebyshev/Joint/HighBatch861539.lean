/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 861539 to 866539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e861539 : Edge :=
  ⟨861539, 861460856494600496, 861467021221729155, 1018845896939750, 1018858338951882⟩

private def e866539 : Edge :=
  ⟨866539, 866648357554937652, 866654560527808931, 1025680005678137, 1025692448270876⟩

private def extra861539 : ℕ → ℕ
  | 861539 => 663
  | 862203 => 607
  | 862811 => 749
  | 863561 => 661
  | 864223 => 687
  | 864911 => 625
  | 865537 => 545
  | 866083 => 455
  | _ => 0

private theorem part861539 : Segment Valid highEstimate e861539 e866539 := by
  apply gcd_batch (by decide) (by decide) extra861539 8
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [861539,866539). -/
theorem batch861539 :
    Segment Valid highEstimate
      ⟨861539, 861460856494600496, 861467021221729155, 1018845896939750, 1018858338951882⟩
      ⟨866539, 866648357554937652, 866654560527808931, 1025680005678137, 1025692448270876⟩ := by
  exact part861539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
