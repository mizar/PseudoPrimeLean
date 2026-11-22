/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 561539 to 566539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e561539 : Edge :=
  ⟨561539, 561513965587696661, 561517999202475834, 836512506291081, 836523164081411⟩

private def e566539 : Edge :=
  ⟨566539, 566367486898526859, 566371550732653198, 843133909163522, 843144774634924⟩

private def extra561539 : ℕ → ℕ
  | 561539 => 573
  | 562113 => 423
  | 562537 => 476
  | 563014 => 569
  | 563584 => 515
  | 564100 => 456
  | 564557 => 516
  | 565074 => 463
  | 565538 => 529
  | 566068 => 470
  | _ => 0

private theorem part561539 : Segment Valid highEstimate e561539 e566539 := by
  apply gcd_batch (by decide) (by decide) extra561539 10
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [561539,566539). -/
theorem batch561539 :
    Segment Valid highEstimate
      ⟨561539, 561513965587696661, 561517999202475834, 836512506291081, 836523164081411⟩
      ⟨566539, 566367486898526859, 566371550732653198, 843133909163522, 843144774634924⟩ := by
  exact part561539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
