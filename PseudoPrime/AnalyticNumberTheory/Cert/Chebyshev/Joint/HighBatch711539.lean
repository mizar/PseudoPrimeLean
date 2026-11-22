/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 711539 to 716539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e711539 : Edge :=
  ⟨711539, 711639544889051334, 711644881009029805, 942304906054199, 942316637549039⟩

private def e716539 : Edge :=
  ⟨716539, 716572739177339342, 716578109465859762, 942304906054199, 942316637549039⟩

private def extra711539 : ℕ → ℕ
  | 711539 => 527
  | 712067 => 535
  | 712603 => 567
  | 713171 => 565
  | 713737 => 705
  | 714443 => 648
  | 715092 => 634
  | 715727 => 671
  | 716399 => 139
  | _ => 0

private theorem part711539 : Segment Valid highEstimate e711539 e716539 := by
  apply gcd_batch (by decide) (by decide) extra711539 9
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [711539,716539). -/
theorem batch711539 :
    Segment Valid highEstimate
      ⟨711539, 711639544889051334, 711644881009029805, 942304906054199, 942316637549039⟩
      ⟨716539, 716572739177339342, 716578109465859762, 942304906054199, 942316637549039⟩ := by
  exact part711539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
