/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 706539 to 711539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e706539 : Edge :=
  ⟨706539, 706503475488883296, 706508802955717116, 938937610224217, 938949341719052⟩

private def e711539 : Edge :=
  ⟨711539, 711639544889051334, 711644881009029805, 942304906054199, 942316637549039⟩

private def extra706539 : ℕ → ℕ
  | 706539 => 636
  | 707176 => 672
  | 707849 => 587
  | 708437 => 679
  | 709117 => 651
  | 709769 => 619
  | 710389 => 543
  | 710933 => 575
  | 711509 => 29
  | _ => 0

private theorem part706539 : Segment Valid highEstimate e706539 e711539 := by
  apply gcd_batch (by decide) (by decide) extra706539 9
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [706539,711539). -/
theorem batch706539 :
    Segment Valid highEstimate
      ⟨706539, 706503475488883296, 706508802955717116, 938937610224217, 938949341719052⟩
      ⟨711539, 711639544889051334, 711644881009029805, 942304906054199, 942316637549039⟩ := by
  exact part706539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
