/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 766539 to 771539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e766539 : Edge :=
  ⟨766539, 766515860919167815, 766521545846317146, 969323284128657, 969335329903535⟩

private def e771539 : Edge :=
  ⟨771539, 771564332433043628, 771570066296020882, 976099789998232, 976111948968637⟩

private def extra766539 : ℕ → ℕ
  | 766539 => 676
  | 767216 => 650
  | 767867 => 663
  | 768531 => 677
  | 769209 => 657
  | 769867 => 636
  | 770504 => 650
  | 771155 => 383
  | _ => 0

private theorem part766539 : Segment Valid highEstimate e766539 e771539 := by
  apply gcd_batch (by decide) (by decide) extra766539 8
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [766539,771539). -/
theorem batch766539 :
    Segment Valid highEstimate
      ⟨766539, 766515860919167815, 766521545846317146, 969323284128657, 969335329903535⟩
      ⟨771539, 771564332433043628, 771570066296020882, 976099789998232, 976111948968637⟩ := by
  exact part766539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
