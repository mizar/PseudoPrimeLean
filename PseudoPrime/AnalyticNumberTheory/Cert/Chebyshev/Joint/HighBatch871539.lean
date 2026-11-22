/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 871539 to 876539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e871539 : Edge :=
  ⟨871539, 871708131014049436, 871714357291642464, 1025680005678137, 1025692448270876⟩

private def e876539 : Edge :=
  ⟨876539, 876756398738757828, 876762633607524403, 1025680005678137, 1025692448270876⟩

private def extra871539 : ℕ → ℕ
  | 871539 => 601
  | 872141 => 481
  | 872623 => 627
  | 873251 => 661
  | 873913 => 723
  | 874637 => 679
  | 875317 => 575
  | 875893 => 479
  | 876373 => 165
  | _ => 0

private theorem part871539 : Segment Valid highEstimate e871539 e876539 := by
  apply gcd_batch (by decide) (by decide) extra871539 9
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [871539,876539). -/
theorem batch871539 :
    Segment Valid highEstimate
      ⟨871539, 871708131014049436, 871714357291642464, 1025680005678137, 1025692448270876⟩
      ⟨876539, 876756398738757828, 876762633607524403, 1025680005678137, 1025692448270876⟩ := by
  exact part871539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
