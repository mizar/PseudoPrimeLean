/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 756539 to 761539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e756539 : Edge :=
  ⟨756539, 756263657967447517, 756269295156134704, 969323284128657, 969335329903535⟩

private def e761539 : Edge :=
  ⟨761539, 761395293678725090, 761400941553885399, 969323284128657, 969335329903535⟩

private def extra756539 : ℕ → ℕ
  | 756539 => 419
  | 756959 => 378
  | 757338 => 338
  | 757677 => 324
  | 758002 => 297
  | 758300 => 338
  | 758639 => 337
  | 758977 => 379
  | 759357 => 337
  | 759695 => 419
  | 760115 => 378
  | 760494 => 433
  | 760928 => 446
  | 761375 => 163
  | _ => 0

private theorem part756539 : Segment Valid highEstimate e756539 e761539 := by
  apply gcd_batch (by decide) (by decide) extra756539 14
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [756539,761539). -/
theorem batch756539 :
    Segment Valid highEstimate
      ⟨756539, 756263657967447517, 756269295156134704, 969323284128657, 969335329903535⟩
      ⟨761539, 761395293678725090, 761400941553885399, 969323284128657, 969335329903535⟩ := by
  exact part756539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
