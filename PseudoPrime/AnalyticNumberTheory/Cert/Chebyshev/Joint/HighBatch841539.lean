/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 841539 to 846539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e841539 : Edge :=
  ⟨841539, 841613699477514666, 841619776629808475, 1012022610967268, 1012035023523210⟩

private def e846539 : Edge :=
  ⟨846539, 846587630139856280, 846593726294926399, 1018845896939750, 1018858338951882⟩

private def extra841539 : ℕ → ℕ
  | 841539 => 643
  | 842183 => 607
  | 842791 => 591
  | 843383 => 677
  | 844061 => 547
  | 844609 => 587
  | 845197 => 681
  | 845879 => 659
  | _ => 0

private theorem part841539 : Segment Valid highEstimate e841539 e846539 := by
  apply gcd_batch (by decide) (by decide) extra841539 8
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [841539,846539). -/
theorem batch841539 :
    Segment Valid highEstimate
      ⟨841539, 841613699477514666, 841619776629808475, 1012022610967268, 1012035023523210⟩
      ⟨846539, 846587630139856280, 846593726294926399, 1018845896939750, 1018858338951882⟩ := by
  exact part841539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
