/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 786539 to 791539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e786539 : Edge :=
  ⟨786539, 786473191412509356, 786479016874675260, 989664172811091, 989676338238130⟩

private def e791539 : Edge :=
  ⟨791539, 791531199979727438, 791537028115218617, 996452017626611, 996464214691058⟩

private def extra786539 : ℕ → ℕ
  | 786539 => 642
  | 787182 => 658
  | 787841 => 685
  | 788527 => 641
  | 789169 => 713
  | 789883 => 701
  | 790585 => 675
  | 791261 => 277
  | _ => 0

private theorem part786539 : Segment Valid highEstimate e786539 e791539 := by
  apply gcd_batch (by decide) (by decide) extra786539 8
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [786539,791539). -/
theorem batch786539 :
    Segment Valid highEstimate
      ⟨786539, 786473191412509356, 786479016874675260, 989664172811091, 989676338238130⟩
      ⟨791539, 791531199979727438, 791537028115218617, 996452017626611, 996464214691058⟩ := by
  exact part786539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
