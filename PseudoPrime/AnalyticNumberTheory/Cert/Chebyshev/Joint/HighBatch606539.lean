/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 606539 to 611539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e606539 : Edge :=
  ⟨606539, 606655141633597232, 606659682153251639, 874112115045486, 874123170639620⟩

private def e611539 : Edge :=
  ⟨611539, 611703256604477877, 611707802194096507, 874112115045486, 874123170639620⟩

private def extra606539 : ℕ → ℕ
  | 606539 => 467
  | 607007 => 355
  | 607363 => 479
  | 607843 => 503
  | 608347 => 471
  | 608819 => 421
  | 609241 => 357
  | 609599 => 379
  | 609979 => 467
  | 610447 => 399
  | 610847 => 415
  | 611263 => 275
  | _ => 0

private theorem part606539 : Segment Valid highEstimate e606539 e611539 := by
  apply gcd_batch (by decide) (by decide) extra606539 12
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [606539,611539). -/
theorem batch606539 :
    Segment Valid highEstimate
      ⟨606539, 606655141633597232, 606659682153251639, 874112115045486, 874123170639620⟩
      ⟨611539, 611703256604477877, 611707802194096507, 874112115045486, 874123170639620⟩ := by
  exact part606539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
