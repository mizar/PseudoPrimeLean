/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 686539 to 691539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e686539 : Edge :=
  ⟨686539, 686412368585099605, 686417547019080632, 920996545007128, 921008049638333⟩

private def e691539 : Edge :=
  ⟨691539, 691312311202672969, 691317524145104807, 927716763830316, 927728395365848⟩

private def extra686539 : ℕ → ℕ
  | 686539 => 535
  | 687075 => 550
  | 687626 => 625
  | 688252 => 617
  | 688870 => 618
  | 689489 => 631
  | 690121 => 631
  | 690753 => 537
  | 691291 => 247
  | _ => 0

private theorem part686539 : Segment Valid highEstimate e686539 e691539 := by
  apply gcd_batch (by decide) (by decide) extra686539 9
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [686539,691539). -/
theorem batch686539 :
    Segment Valid highEstimate
      ⟨686539, 686412368585099605, 686417547019080632, 920996545007128, 921008049638333⟩
      ⟨691539, 691312311202672969, 691317524145104807, 927716763830316, 927728395365848⟩ := by
  exact part686539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
