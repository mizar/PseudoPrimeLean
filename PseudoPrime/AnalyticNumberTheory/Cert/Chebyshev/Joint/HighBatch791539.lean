/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 791539 to 796539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e791539 : Edge :=
  ⟨791539, 791531199979727438, 791537028115218617, 996452017626611, 996464214691058⟩

private def e796539 : Edge :=
  ⟨796539, 796625522429139383, 796631368640420656, 996452017626611, 996464214691058⟩

private def extra791539 : ℕ → ℕ
  | 791539 => 701
  | 792241 => 639
  | 792881 => 709
  | 793591 => 569
  | 794161 => 579
  | 794741 => 607
  | 795349 => 593
  | 795943 => 595
  | _ => 0

private theorem part791539 : Segment Valid highEstimate e791539 e796539 := by
  apply gcd_batch (by decide) (by decide) extra791539 8
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [791539,796539). -/
theorem batch791539 :
    Segment Valid highEstimate
      ⟨791539, 791531199979727438, 791537028115218617, 996452017626611, 996464214691058⟩
      ⟨796539, 796625522429139383, 796631368640420656, 996452017626611, 996464214691058⟩ := by
  exact part791539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
