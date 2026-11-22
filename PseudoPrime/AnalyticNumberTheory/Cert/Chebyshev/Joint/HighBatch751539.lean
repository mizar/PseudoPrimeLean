/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 751539 to 756539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e751539 : Edge :=
  ⟨751539, 751242872242326510, 751248475187821155, 969323284128657, 969335329903535⟩

private def e756539 : Edge :=
  ⟨756539, 756263657967447517, 756269295156134704, 969323284128657, 969335329903535⟩

private def extra751539 : ℕ → ℕ
  | 751539 => 396
  | 751936 => 459
  | 752396 => 473
  | 752870 => 473
  | 753344 => 378
  | 753723 => 432
  | 754156 => 473
  | 754630 => 514
  | 755145 => 527
  | 755673 => 527
  | 756201 => 337
  | _ => 0

private theorem part751539 : Segment Valid highEstimate e751539 e756539 := by
  apply gcd_batch (by decide) (by decide) extra751539 11
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [751539,756539). -/
theorem batch751539 :
    Segment Valid highEstimate
      ⟨751539, 751242872242326510, 751248475187821155, 969323284128657, 969335329903535⟩
      ⟨756539, 756263657967447517, 756269295156134704, 969323284128657, 969335329903535⟩ := by
  exact part751539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
