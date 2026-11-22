/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 646539 to 651539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e646539 : Edge :=
  ⟨646539, 646310721377617524, 646315561248544874, 887461196452993, 887472396843589⟩

private def e651539 : Edge :=
  ⟨651539, 651316027203783601, 651320913964596621, 887461196452993, 887472396843589⟩

private def extra646539 : ℕ → ℕ
  | 646539 => 414
  | 646954 => 400
  | 647355 => 414
  | 647770 => 481
  | 648252 => 521
  | 648774 => 468
  | 649243 => 441
  | 649685 => 521
  | 650207 => 508
  | 650716 => 428
  | 651145 => 393
  | _ => 0

private theorem part646539 : Segment Valid highEstimate e646539 e651539 := by
  apply gcd_batch (by decide) (by decide) extra646539 11
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [646539,651539). -/
theorem batch646539 :
    Segment Valid highEstimate
      ⟨646539, 646310721377617524, 646315561248544874, 887461196452993, 887472396843589⟩
      ⟨651539, 651316027203783601, 651320913964596621, 887461196452993, 887472396843589⟩ := by
  exact part646539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
