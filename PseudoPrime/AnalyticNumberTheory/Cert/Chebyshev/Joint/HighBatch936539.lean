/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 936539 to 941539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e936539 : Edge :=
  ⟨936539, 936770254416712369, 936776745537277321, 1067965440766627, 1067978159843455⟩

private def e941539 : Edge :=
  ⟨941539, 941762472428818080, 941768969632513838, 1067965440766627, 1067978159843455⟩

private def extra936539 : ℕ → ℕ
  | 936539 => 527
  | 937067 => 599
  | 937667 => 551
  | 938219 => 611
  | 938831 => 599
  | 939431 => 641
  | 940073 => 659
  | 940733 => 595
  | 941329 => 209
  | _ => 0

private theorem part936539 : Segment Valid highEstimate e936539 e941539 := by
  apply gcd_batch (by decide) (by decide) extra936539 9
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [936539,941539). -/
theorem batch936539 :
    Segment Valid highEstimate
      ⟨936539, 936770254416712369, 936776745537277321, 1067965440766627, 1067978159843455⟩
      ⟨941539, 941762472428818080, 941768969632513838, 1067965440766627, 1067978159843455⟩ := by
  exact part936539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
