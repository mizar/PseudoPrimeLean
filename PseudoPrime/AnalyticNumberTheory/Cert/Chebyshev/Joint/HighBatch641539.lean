/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 641539 to 646539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e641539 : Edge :=
  ⟨641539, 641335004472386096, 641339831537883740, 887461196452993, 887472396843589⟩

private def e646539 : Edge :=
  ⟨646539, 646310721377617524, 646315561248544874, 887461196452993, 887472396843589⟩

private def extra641539 : ℕ → ℕ
  | 641539 => 435
  | 641975 => 441
  | 642417 => 387
  | 642805 => 320
  | 643126 => 374
  | 643501 => 293
  | 643795 => 294
  | 644090 => 280
  | 644371 => 333
  | 644705 => 387
  | 645093 => 481
  | 645575 => 401
  | 645977 => 440
  | 646418 => 120
  | _ => 0

private theorem part641539 : Segment Valid highEstimate e641539 e646539 := by
  apply gcd_batch (by decide) (by decide) extra641539 14
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [641539,646539). -/
theorem batch641539 :
    Segment Valid highEstimate
      ⟨641539, 641335004472386096, 641339831537883740, 887461196452993, 887472396843589⟩
      ⟨646539, 646310721377617524, 646315561248544874, 887461196452993, 887472396843589⟩ := by
  exact part641539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
