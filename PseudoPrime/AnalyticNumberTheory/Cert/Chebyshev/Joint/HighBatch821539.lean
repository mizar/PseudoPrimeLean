/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 821539 to 826539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e821539 : Edge :=
  ⟨821539, 821588046766904406, 821594041367152941, 996452017626611, 996464214691058⟩

private def e826539 : Edge :=
  ⟨826539, 826800389560951416, 826806391435947923, 1005208069614610, 1005220342038805⟩

private def extra821539 : ℕ → ℕ
  | 821539 => 689
  | 822229 => 563
  | 822793 => 563
  | 823357 => 483
  | 823841 => 559
  | 824401 => 537
  | 824939 => 457
  | 825397 => 423
  | 825821 => 461
  | 826283 => 255
  | _ => 0

private theorem part821539 : Segment Valid highEstimate e821539 e826539 := by
  apply gcd_batch (by decide) (by decide) extra821539 10
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [821539,826539). -/
theorem batch821539 :
    Segment Valid highEstimate
      ⟨821539, 821588046766904406, 821594041367152941, 996452017626611, 996464214691058⟩
      ⟨826539, 826800389560951416, 826806391435947923, 1005208069614610, 1005220342038805⟩ := by
  exact part821539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
