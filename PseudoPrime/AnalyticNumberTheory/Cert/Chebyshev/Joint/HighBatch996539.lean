/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 996539 to 1000000 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e996539 : Edge :=
  ⟨996539, 996077836842586904, 996084532522276670, 1102422326452684, 1102435268224133⟩

private def e1000000 : Edge :=
  ⟨1000000, 999586518104918955, 999593238652839812, 1102422326452684, 1102435268224133⟩

private def extra996539 : ℕ → ℕ
  | 996539 => 350
  | 996890 => 358
  | 997249 => 428
  | 997678 => 455
  | 998134 => 468
  | 998603 => 428
  | 999032 => 496
  | 999529 => 442
  | 999972 => 27
  | _ => 0

private theorem part996539 : Segment Valid highEstimate e996539 e1000000 := by
  apply gcd_batch (by decide) (by decide) extra996539 9
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [996539,1000000). -/
theorem batch996539 :
    Segment Valid highEstimate
      ⟨996539, 996077836842586904, 996084532522276670, 1102422326452684, 1102435268224133⟩
      ⟨1000000, 999586518104918955, 999593238652839812, 1102422326452684, 1102435268224133⟩ := by
  exact part996539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
