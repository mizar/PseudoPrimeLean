/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 746539 to 751539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e746539 : Edge :=
  ⟨746539, 746305661307613763, 746311216772775337, 969323284128657, 969335329903535⟩

private def e751539 : Edge :=
  ⟨751539, 751242872242326510, 751248475187821155, 969323284128657, 969335329903535⟩

private def extra746539 : ℕ → ℕ
  | 746539 => 457
  | 746997 => 432
  | 747430 => 364
  | 747795 => 351
  | 748147 => 350
  | 748498 => 338
  | 748837 => 418
  | 749256 => 432
  | 749689 => 378
  | 750068 => 365
  | 750434 => 351
  | 750786 => 310
  | 751097 => 310
  | 751408 => 130
  | _ => 0

private theorem part746539 : Segment Valid highEstimate e746539 e751539 := by
  apply gcd_batch (by decide) (by decide) extra746539 14
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [746539,751539). -/
theorem batch746539 :
    Segment Valid highEstimate
      ⟨746539, 746305661307613763, 746311216772775337, 969323284128657, 969335329903535⟩
      ⟨751539, 751242872242326510, 751248475187821155, 969323284128657, 969335329903535⟩ := by
  exact part746539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
