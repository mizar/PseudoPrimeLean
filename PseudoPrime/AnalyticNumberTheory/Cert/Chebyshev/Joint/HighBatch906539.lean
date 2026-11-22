/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 906539 to 911539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e906539 : Edge :=
  ⟨906539, 906603126071419620, 906609492378114731, 1046222929973740, 1046235522765251⟩

private def e911539 : Edge :=
  ⟨911539, 911892214537799288, 911898596014063683, 1053082544590572, 1053095182829703⟩

private def extra906539 : ℕ → ℕ
  | 906539 => 659
  | 907199 => 557
  | 907757 => 595
  | 908353 => 495
  | 908849 => 431
  | 909281 => 355
  | 909637 => 333
  | 909971 => 307
  | 910279 => 411
  | 910691 => 455
  | 911147 => 391
  | _ => 0

private theorem part906539 : Segment Valid highEstimate e906539 e911539 := by
  apply gcd_batch (by decide) (by decide) extra906539 11
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [906539,911539). -/
theorem batch906539 :
    Segment Valid highEstimate
      ⟨906539, 906603126071419620, 906609492378114731, 1046222929973740, 1046235522765251⟩
      ⟨911539, 911892214537799288, 911898596014063683, 1053082544590572, 1053095182829703⟩ := by
  exact part906539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
