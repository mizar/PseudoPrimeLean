/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 506539 to 511539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e506539 : Edge :=
  ⟨506539, 506605502941265984, 506609079491755194, 801740825039943, 801750992042056⟩

private def e511539 : Edge :=
  ⟨511539, 511572547950454709, 511576138182946101, 801740825039943, 801750992042056⟩

private def extra506539 : ℕ → ℕ
  | 506539 => 509
  | 507049 => 539
  | 507589 => 513
  | 508103 => 533
  | 508637 => 589
  | 509227 => 550
  | 509778 => 508
  | 510287 => 559
  | 510847 => 561
  | 511409 => 129
  | _ => 0

private theorem part506539 : Segment Valid highEstimate e506539 e511539 := by
  apply gcd_batch (by decide) (by decide) extra506539 10
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [506539,511539). -/
theorem batch506539 :
    Segment Valid highEstimate
      ⟨506539, 506605502941265984, 506609079491755194, 801740825039943, 801750992042056⟩
      ⟨511539, 511572547950454709, 511576138182946101, 801740825039943, 801750992042056⟩ := by
  exact part506539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
