/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 831539 to 836539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e831539 : Edge :=
  ⟨831539, 831686021554378298, 831692049791385777, 1012022610967268, 1012035023523210⟩

private def e836539 : Edge :=
  ⟨836539, 836744205537533115, 836750279065628673, 1012022610967268, 1012035023523210⟩

private def extra831539 : ℕ → ℕ
  | 831539 => 427
  | 831967 => 443
  | 832411 => 351
  | 832763 => 337
  | 833101 => 365
  | 833467 => 389
  | 833857 => 425
  | 834283 => 489
  | 834773 => 545
  | 835319 => 521
  | 835841 => 485
  | 836327 => 211
  | _ => 0

private theorem part831539 : Segment Valid highEstimate e831539 e836539 := by
  apply gcd_batch (by decide) (by decide) extra831539 12
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [831539,836539). -/
theorem batch831539 :
    Segment Valid highEstimate
      ⟨831539, 831686021554378298, 831692049791385777, 1012022610967268, 1012035023523210⟩
      ⟨836539, 836744205537533115, 836750279065628673, 1012022610967268, 1012035023523210⟩ := by
  exact part831539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
