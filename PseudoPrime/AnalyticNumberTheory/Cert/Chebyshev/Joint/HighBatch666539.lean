/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 666539 to 671539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e666539 : Edge :=
  ⟨666539, 666416161902772199, 666421165805543381, 900855262095811, 900866620298927⟩

private def e671539 : Edge :=
  ⟨671539, 671325556054094871, 671330641003367806, 900855262095811, 900866620298927⟩

private def extra666539 : ℕ → ℕ
  | 666539 => 529
  | 667069 => 509
  | 667579 => 549
  | 668129 => 522
  | 668652 => 402
  | 669055 => 402
  | 669458 => 415
  | 669874 => 401
  | 670276 => 415
  | 670692 => 429
  | 671122 => 415
  | _ => 0

private theorem part666539 : Segment Valid highEstimate e666539 e671539 := by
  apply gcd_batch (by decide) (by decide) extra666539 12
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [666539,671539). -/
theorem batch666539 :
    Segment Valid highEstimate
      ⟨666539, 666416161902772199, 666421165805543381, 900855262095811, 900866620298927⟩
      ⟨671539, 671325556054094871, 671330641003367806, 900855262095811, 900866620298927⟩ := by
  exact part666539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
