/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 956539 to 961539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e956539 : Edge :=
  ⟨956539, 956516597372522837, 956523151516747531, 1081728253389386, 1081741038637830⟩

private def e961539 : Edge :=
  ⟨961539, 961392508433358735, 961399078287689346, 1081728253389386, 1081741038637830⟩

private def extra956539 : ℕ → ℕ
  | 956539 => 759
  | 957299 => 674
  | 957974 => 605
  | 958580 => 674
  | 959255 => 619
  | 959875 => 619
  | 960495 => 564
  | 961060 => 478
  | _ => 0

private theorem part956539 : Segment Valid highEstimate e956539 e961539 := by
  apply gcd_batch (by decide) (by decide) extra956539 8
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [956539,961539). -/
theorem batch956539 :
    Segment Valid highEstimate
      ⟨956539, 956516597372522837, 956523151516747531, 1081728253389386, 1081741038637830⟩
      ⟨961539, 961392508433358735, 961399078287689346, 1081728253389386, 1081741038637830⟩ := by
  exact part956539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
