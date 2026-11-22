/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 566539 to 571539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e566539 : Edge :=
  ⟨566539, 566367486898526859, 566371550732653198, 843133909163522, 843144774634924⟩

private def e571539 : Edge :=
  ⟨571539, 571416396792137200, 571420550315734517, 843133909163522, 843144774634924⟩

private def extra566539 : ℕ → ℕ
  | 566539 => 443
  | 566983 => 449
  | 567433 => 370
  | 567804 => 371
  | 568176 => 410
  | 568587 => 383
  | 568971 => 330
  | 569302 => 424
  | 569727 => 370
  | 570098 => 476
  | 570575 => 517
  | 571093 => 445
  | _ => 0

private theorem part566539 : Segment Valid highEstimate e566539 e571539 := by
  apply gcd_batch (by decide) (by decide) extra566539 12
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [566539,571539). -/
theorem batch566539 :
    Segment Valid highEstimate
      ⟨566539, 566367486898526859, 566371550732653198, 843133909163522, 843144774634924⟩
      ⟨571539, 571416396792137200, 571420550315734517, 843133909163522, 843144774634924⟩ := by
  exact part566539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
