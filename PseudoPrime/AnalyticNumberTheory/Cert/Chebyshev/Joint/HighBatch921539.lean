/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 921539 to 926539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e921539 : Edge :=
  ⟨921539, 921671437706796767, 921677866978525237, 1057657255195228, 1057669947687839⟩

private def e926539 : Edge :=
  ⟨926539, 926922224503257658, 926928663976648094, 1061091242399709, 1061103934892325⟩

private def extra921539 : ℕ → ℕ
  | 921539 => 559
  | 922099 => 543
  | 922643 => 605
  | 923249 => 599
  | 923849 => 547
  | 924397 => 443
  | 924841 => 399
  | 925241 => 379
  | 925621 => 395
  | 926017 => 381
  | 926399 => 139
  | _ => 0

private theorem part921539 : Segment Valid highEstimate e921539 e926539 := by
  apply gcd_batch (by decide) (by decide) extra921539 11
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [921539,926539). -/
theorem batch921539 :
    Segment Valid highEstimate
      ⟨921539, 921671437706796767, 921677866978525237, 1057657255195228, 1057669947687839⟩
      ⟨926539, 926922224503257658, 926928663976648094, 1061091242399709, 1061103934892325⟩ := by
  exact part921539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
