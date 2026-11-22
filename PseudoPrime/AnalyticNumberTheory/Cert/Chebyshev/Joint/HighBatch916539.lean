/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 916539 to 921539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e916539 : Edge :=
  ⟨916539, 916673325082273885, 916679743113070684, 1057657255195228, 1057669947687839⟩

private def e921539 : Edge :=
  ⟨921539, 921671437706796767, 921677866978525237, 1057657255195228, 1057669947687839⟩

private def extra916539 : ℕ → ℕ
  | 916539 => 669
  | 917209 => 617
  | 917827 => 569
  | 918397 => 573
  | 918971 => 599
  | 919571 => 637
  | 920209 => 617
  | 920827 => 635
  | 921463 => 75
  | _ => 0

private theorem part916539 : Segment Valid highEstimate e916539 e921539 := by
  apply gcd_batch (by decide) (by decide) extra916539 9
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [916539,921539). -/
theorem batch916539 :
    Segment Valid highEstimate
      ⟨916539, 916673325082273885, 916679743113070684, 1057657255195228, 1057669947687839⟩
      ⟨921539, 921671437706796767, 921677866978525237, 1057657255195228, 1057669947687839⟩ := by
  exact part916539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
