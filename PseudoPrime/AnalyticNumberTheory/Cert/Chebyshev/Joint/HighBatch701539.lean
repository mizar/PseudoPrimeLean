/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 701539 to 706539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e701539 : Edge :=
  ⟨701539, 701362245240628828, 701367519381235723, 927716763830316, 927728395365848⟩

private def e706539 : Edge :=
  ⟨706539, 706503475488883296, 706508802955717116, 938937610224217, 938949341719052⟩

private def extra701539 : ℕ → ℕ
  | 701539 => 492
  | 702032 => 443
  | 702476 => 498
  | 702975 => 524
  | 703500 => 538
  | 704039 => 531
  | 704571 => 578
  | 705150 => 691
  | 705842 => 605
  | 706448 => 90
  | _ => 0

private theorem part701539 : Segment Valid highEstimate e701539 e706539 := by
  apply gcd_batch (by decide) (by decide) extra701539 10
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [701539,706539). -/
theorem batch701539 :
    Segment Valid highEstimate
      ⟨701539, 701362245240628828, 701367519381235723, 927716763830316, 927728395365848⟩
      ⟨706539, 706503475488883296, 706508802955717116, 938937610224217, 938949341719052⟩ := by
  exact part701539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
