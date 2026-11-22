/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 571539 to 576539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e571539 : Edge :=
  ⟨571539, 571416396792137200, 571420550315734517, 843133909163522, 843144774634924⟩

private def e576539 : Edge :=
  ⟨576539, 576506182665345390, 576510394117609504, 854182112328166, 854193074264263⟩

private def extra571539 : ℕ → ℕ
  | 571539 => 481
  | 572021 => 481
  | 572503 => 543
  | 573047 => 622
  | 573670 => 550
  | 574221 => 596
  | 574818 => 583
  | 575402 => 516
  | 575919 => 530
  | 576450 => 88
  | _ => 0

private theorem part571539 : Segment Valid highEstimate e571539 e576539 := by
  apply gcd_batch (by decide) (by decide) extra571539 10
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [571539,576539). -/
theorem batch571539 :
    Segment Valid highEstimate
      ⟨571539, 571416396792137200, 571420550315734517, 843133909163522, 843144774634924⟩
      ⟨576539, 576506182665345390, 576510394117609504, 854182112328166, 854193074264263⟩ := by
  exact part571539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
