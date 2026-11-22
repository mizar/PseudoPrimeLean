/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 696539 to 701539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e696539 : Edge :=
  ⟨696539, 696477191823668755, 696482419560906906, 927716763830316, 927728395365848⟩

private def e701539 : Edge :=
  ⟨701539, 701362245240628828, 701367519381235723, 927716763830316, 927728395365848⟩

private def extra696539 : ℕ → ℕ
  | 696539 => 605
  | 697145 => 641
  | 697787 => 689
  | 698477 => 619
  | 699097 => 510
  | 699608 => 565
  | 700174 => 470
  | 700645 => 511
  | 701157 => 381
  | _ => 0

private theorem part696539 : Segment Valid highEstimate e696539 e701539 := by
  apply gcd_batch (by decide) (by decide) extra696539 9
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [696539,701539). -/
theorem batch696539 :
    Segment Valid highEstimate
      ⟨696539, 696477191823668755, 696482419560906906, 927716763830316, 927728395365848⟩
      ⟨701539, 701362245240628828, 701367519381235723, 927716763830316, 927728395365848⟩ := by
  exact part696539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
