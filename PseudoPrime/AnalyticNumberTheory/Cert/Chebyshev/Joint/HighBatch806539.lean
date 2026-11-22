/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 806539 to 811539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e806539 : Edge :=
  ⟨806539, 806712479534722463, 806718393580556253, 996452017626611, 996464214691058⟩

private def e811539 : Edge :=
  ⟨811539, 811596205015537406, 811602130658988895, 996452017626611, 996464214691058⟩

private def extra806539 : ℕ → ℕ
  | 806539 => 647
  | 807187 => 683
  | 807871 => 725
  | 808597 => 711
  | 809309 => 683
  | 809993 => 577
  | 810571 => 635
  | 811207 => 331
  | _ => 0

private theorem part806539 : Segment Valid highEstimate e806539 e811539 := by
  apply gcd_batch (by decide) (by decide) extra806539 8
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [806539,811539). -/
theorem batch806539 :
    Segment Valid highEstimate
      ⟨806539, 806712479534722463, 806718393580556253, 996452017626611, 996464214691058⟩
      ⟨811539, 811596205015537406, 811602130658988895, 996452017626611, 996464214691058⟩ := by
  exact part806539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
