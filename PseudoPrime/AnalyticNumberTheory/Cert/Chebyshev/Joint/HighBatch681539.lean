/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 681539 to 686539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e681539 : Edge :=
  ⟨681539, 681474710851515516, 681479826622517843, 914278741120503, 914290154891211⟩

private def e686539 : Edge :=
  ⟨686539, 686412368585099605, 686417547019080632, 920996545007128, 921008049638333⟩

private def extra681539 : ℕ → ℕ
  | 681539 => 608
  | 682148 => 577
  | 682726 => 577
  | 683304 => 443
  | 683748 => 483
  | 684232 => 516
  | 684749 => 497
  | 685247 => 536
  | 685784 => 577
  | 686362 => 176
  | _ => 0

private theorem part681539 : Segment Valid highEstimate e681539 e686539 := by
  apply gcd_batch (by decide) (by decide) extra681539 10
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [681539,686539). -/
theorem batch681539 :
    Segment Valid highEstimate
      ⟨681539, 681474710851515516, 681479826622517843, 914278741120503, 914290154891211⟩
      ⟨686539, 686412368585099605, 686417547019080632, 920996545007128, 921008049638333⟩ := by
  exact part681539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
