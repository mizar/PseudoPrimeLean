/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 576539 to 581539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e576539 : Edge :=
  ⟨576539, 576506182665345390, 576510394117609504, 854182112328166, 854193074264263⟩

private def e581539 : Edge :=
  ⟨581539, 581568358105352654, 581572589078747123, 860816745119682, 860827778673321⟩

private def extra576539 : ℕ → ℕ
  | 576539 => 587
  | 577127 => 596
  | 577724 => 583
  | 578308 => 543
  | 578852 => 636
  | 579489 => 537
  | 580027 => 623
  | 580651 => 557
  | 581209 => 329
  | _ => 0

private theorem part576539 : Segment Valid highEstimate e576539 e581539 := by
  apply gcd_batch (by decide) (by decide) extra576539 9
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [576539,581539). -/
theorem batch576539 :
    Segment Valid highEstimate
      ⟨576539, 576506182665345390, 576510394117609504, 854182112328166, 854193074264263⟩
      ⟨581539, 581568358105352654, 581572589078747123, 860816745119682, 860827778673321⟩ := by
  exact part576539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
