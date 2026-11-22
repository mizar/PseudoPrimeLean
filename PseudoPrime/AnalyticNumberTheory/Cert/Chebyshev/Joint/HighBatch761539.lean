/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 761539 to 766539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e761539 : Edge :=
  ⟨761539, 761395293678725090, 761400941553885399, 969323284128657, 969335329903535⟩

private def e766539 : Edge :=
  ⟨766539, 766515860919167815, 766521545846317146, 969323284128657, 969335329903535⟩

private def extra761539 : ℕ → ℕ
  | 761539 => 553
  | 762093 => 555
  | 762649 => 473
  | 763123 => 487
  | 763611 => 487
  | 764099 => 568
  | 764668 => 514
  | 765183 => 555
  | 765739 => 568
  | 766308 => 230
  | _ => 0

private theorem part761539 : Segment Valid highEstimate e761539 e766539 := by
  apply gcd_batch (by decide) (by decide) extra761539 10
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [761539,766539). -/
theorem batch761539 :
    Segment Valid highEstimate
      ⟨761539, 761395293678725090, 761400941553885399, 969323284128657, 969335329903535⟩
      ⟨766539, 766515860919167815, 766521545846317146, 969323284128657, 969335329903535⟩ := by
  exact part761539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
