/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 546539 to 551539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e546539 : Edge :=
  ⟨546539, 546497036782029497, 546500884131748939, 829901810531116, 829912423093115⟩

private def e551539 : Edge :=
  ⟨551539, 551519086700785211, 551522980868759895, 829901810531116, 829912423093115⟩

private def extra546539 : ℕ → ℕ
  | 546539 => 548
  | 547088 => 502
  | 547591 => 541
  | 548133 => 514
  | 548648 => 515
  | 549164 => 568
  | 549733 => 603
  | 550337 => 585
  | 550923 => 594
  | 551518 => 20
  | _ => 0

private theorem part546539 : Segment Valid highEstimate e546539 e551539 := by
  apply gcd_batch (by decide) (by decide) extra546539 10
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [546539,551539). -/
theorem batch546539 :
    Segment Valid highEstimate
      ⟨546539, 546497036782029497, 546500884131748939, 829901810531116, 829912423093115⟩
      ⟨551539, 551519086700785211, 551522980868759895, 829901810531116, 829912423093115⟩ := by
  exact part546539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
