/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 846539 to 851539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e846539 : Edge :=
  ⟨846539, 846587630139856280, 846593726294926399, 1018845896939750, 1018858338951882⟩

private def e851539 : Edge :=
  ⟨851539, 851611514203447833, 851617658626068577, 1018845896939750, 1018858338951882⟩

private def extra846539 : ℕ → ℕ
  | 846539 => 629
  | 847169 => 647
  | 847817 => 719
  | 848537 => 623
  | 849161 => 695
  | 849857 => 581
  | 850439 => 719
  | 851159 => 379
  | _ => 0

private theorem part846539 : Segment Valid highEstimate e846539 e851539 := by
  apply gcd_batch (by decide) (by decide) extra846539 8
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [846539,851539). -/
theorem batch846539 :
    Segment Valid highEstimate
      ⟨846539, 846587630139856280, 846593726294926399, 1018845896939750, 1018858338951882⟩
      ⟨851539, 851611514203447833, 851617658626068577, 1018845896939750, 1018858338951882⟩ := by
  exact part846539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
