/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 611539 to 616539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e611539 : Edge :=
  ⟨611539, 611703256604477877, 611707802194096507, 874112115045486, 874123170639620⟩

private def e616539 : Edge :=
  ⟨616539, 616861142645614799, 616865721992786208, 874112115045486, 874123170639620⟩

private def extra611539 : ℕ → ℕ
  | 611539 => 453
  | 611993 => 377
  | 612371 => 437
  | 612809 => 419
  | 613229 => 377
  | 613607 => 385
  | 613993 => 443
  | 614437 => 411
  | 614849 => 487
  | 615337 => 423
  | 615761 => 407
  | 616169 => 337
  | 616507 => 31
  | _ => 0

private theorem part611539 : Segment Valid highEstimate e611539 e616539 := by
  apply gcd_batch (by decide) (by decide) extra611539 13
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [611539,616539). -/
theorem batch611539 :
    Segment Valid highEstimate
      ⟨611539, 611703256604477877, 611707802194096507, 874112115045486, 874123170639620⟩
      ⟨616539, 616861142645614799, 616865721992786208, 874112115045486, 874123170639620⟩ := by
  exact part611539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
