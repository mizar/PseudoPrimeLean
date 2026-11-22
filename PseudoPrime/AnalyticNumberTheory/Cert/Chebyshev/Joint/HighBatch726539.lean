/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 726539 to 731539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e726539 : Edge :=
  ⟨726539, 726568256142213967, 726573694285358171, 942304906054199, 942316637549039⟩

private def e731539 : Edge :=
  ⟨731539, 731529303067427572, 731534765250192739, 949053665533654, 949065414411248⟩

private def extra726539 : ℕ → ℕ
  | 726539 => 629
  | 727169 => 607
  | 727777 => 711
  | 728489 => 583
  | 729073 => 587
  | 729661 => 659
  | 730321 => 651
  | 730973 => 565
  | _ => 0

private theorem part726539 : Segment Valid highEstimate e726539 e731539 := by
  apply gcd_batch (by decide) (by decide) extra726539 8
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [726539,731539). -/
theorem batch726539 :
    Segment Valid highEstimate
      ⟨726539, 726568256142213967, 726573694285358171, 942304906054199, 942316637549039⟩
      ⟨731539, 731529303067427572, 731534765250192739, 949053665533654, 949065414411248⟩ := by
  exact part726539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
