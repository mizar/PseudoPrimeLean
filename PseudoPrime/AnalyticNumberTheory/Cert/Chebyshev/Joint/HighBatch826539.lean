/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 826539 to 831539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e826539 : Edge :=
  ⟨826539, 826800389560951416, 826806391435947923, 1005208069614610, 1005220342038805⟩

private def e831539 : Edge :=
  ⟨831539, 831686021554378298, 831692049791385777, 1012022610967268, 1012035023523210⟩

private def extra826539 : ℕ → ℕ
  | 826539 => 381
  | 826921 => 425
  | 827347 => 473
  | 827821 => 399
  | 828221 => 509
  | 828731 => 479
  | 829211 => 521
  | 829733 => 577
  | 830311 => 527
  | 830839 => 533
  | 831373 => 165
  | _ => 0

private theorem part826539 : Segment Valid highEstimate e826539 e831539 := by
  apply gcd_batch (by decide) (by decide) extra826539 11
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [826539,831539). -/
theorem batch826539 :
    Segment Valid highEstimate
      ⟨826539, 826800389560951416, 826806391435947923, 1005208069614610, 1005220342038805⟩
      ⟨831539, 831686021554378298, 831692049791385777, 1012022610967268, 1012035023523210⟩ := by
  exact part826539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
