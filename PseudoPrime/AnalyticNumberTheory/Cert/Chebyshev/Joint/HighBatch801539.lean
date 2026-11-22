/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 801539 to 806539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e801539 : Edge :=
  ⟨801539, 801722201739233966, 801728096680372869, 996452017626611, 996464214691058⟩

private def e806539 : Edge :=
  ⟨806539, 806712479534722463, 806718393580556253, 996452017626611, 996464214691058⟩

private def extra801539 : ℕ → ℕ
  | 801539 => 587
  | 802127 => 623
  | 802751 => 689
  | 803441 => 671
  | 804113 => 653
  | 804767 => 545
  | 805313 => 545
  | 805859 => 511
  | 806371 => 167
  | _ => 0

private theorem part801539 : Segment Valid highEstimate e801539 e806539 := by
  apply gcd_batch (by decide) (by decide) extra801539 9
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [801539,806539). -/
theorem batch801539 :
    Segment Valid highEstimate
      ⟨801539, 801722201739233966, 801728096680372869, 996452017626611, 996464214691058⟩
      ⟨806539, 806712479534722463, 806718393580556253, 996452017626611, 996464214691058⟩ := by
  exact part801539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
