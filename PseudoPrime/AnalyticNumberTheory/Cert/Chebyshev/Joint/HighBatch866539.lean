/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 866539 to 871539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e866539 : Edge :=
  ⟨866539, 866648357554937652, 866654560527808931, 1025680005678137, 1025692448270876⟩

private def e871539 : Edge :=
  ⟨871539, 871708131014049436, 871714357291642464, 1025680005678137, 1025692448270876⟩

private def extra866539 : ℕ → ℕ
  | 866539 => 633
  | 867173 => 545
  | 867719 => 571
  | 868291 => 549
  | 868841 => 479
  | 869321 => 487
  | 869809 => 443
  | 870253 => 449
  | 870703 => 459
  | 871163 => 375
  | _ => 0

private theorem part866539 : Segment Valid highEstimate e866539 e871539 := by
  apply gcd_batch (by decide) (by decide) extra866539 10
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [866539,871539). -/
theorem batch866539 :
    Segment Valid highEstimate
      ⟨866539, 866648357554937652, 866654560527808931, 1025680005678137, 1025692448270876⟩
      ⟨871539, 871708131014049436, 871714357291642464, 1025680005678137, 1025692448270876⟩ := by
  exact part866539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
