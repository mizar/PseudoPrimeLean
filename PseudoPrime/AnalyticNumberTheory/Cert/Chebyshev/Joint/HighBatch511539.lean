/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 511539 to 516539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e511539 : Edge :=
  ⟨511539, 511572547950454709, 511576138182946101, 801740825039943, 801750992042056⟩

private def e516539 : Edge :=
  ⟨516539, 516490684436095305, 516494298335432352, 801740825039943, 801750992042056⟩

private def extra511539 : ℕ → ℕ
  | 511539 => 553
  | 512093 => 590
  | 512684 => 512
  | 513197 => 563
  | 513761 => 547
  | 514309 => 531
  | 514841 => 618
  | 515460 => 473
  | 515934 => 486
  | 516421 => 117
  | _ => 0

private theorem part511539 : Segment Valid highEstimate e511539 e516539 := by
  apply gcd_batch (by decide) (by decide) extra511539 10
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [511539,516539). -/
theorem batch511539 :
    Segment Valid highEstimate
      ⟨511539, 511572547950454709, 511576138182946101, 801740825039943, 801750992042056⟩
      ⟨516539, 516490684436095305, 516494298335432352, 801740825039943, 801750992042056⟩ := by
  exact part511539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
