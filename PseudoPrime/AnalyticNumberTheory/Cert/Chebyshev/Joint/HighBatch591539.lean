/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 591539 to 596539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e591539 : Edge :=
  ⟨591539, 591589524179017132, 591593905744761192, 867461836088443, 867472870489804⟩

private def e596539 : Edge :=
  ⟨596539, 596668087217080912, 596672479552492739, 867461836088443, 867472870489804⟩

private def extra591539 : ℕ → ℕ
  | 591539 => 599
  | 592139 => 541
  | 592681 => 527
  | 593209 => 431
  | 593641 => 537
  | 594179 => 487
  | 594667 => 449
  | 595117 => 401
  | 595519 => 447
  | 595967 => 451
  | 596419 => 119
  | _ => 0

private theorem part591539 : Segment Valid highEstimate e591539 e596539 := by
  apply gcd_batch (by decide) (by decide) extra591539 11
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [591539,596539). -/
theorem batch591539 :
    Segment Valid highEstimate
      ⟨591539, 591589524179017132, 591593905744761192, 867461836088443, 867472870489804⟩
      ⟨596539, 596668087217080912, 596672479552492739, 867461836088443, 867472870489804⟩ := by
  exact part591539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
