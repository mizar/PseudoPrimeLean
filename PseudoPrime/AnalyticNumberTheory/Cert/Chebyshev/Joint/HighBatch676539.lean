/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 676539 to 681539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e676539 : Edge :=
  ⟨676539, 676351726654129048, 676356818643495776, 907565785128918, 907577162104873⟩

private def e681539 : Edge :=
  ⟨681539, 681474710851515516, 681479826622517843, 914278741120503, 914290154891211⟩

private def extra676539 : ℕ → ℕ
  | 676539 => 469
  | 677009 => 470
  | 677480 => 462
  | 677943 => 335
  | 678279 => 308
  | 678588 => 348
  | 678937 => 416
  | 679354 => 415
  | 679770 => 456
  | 680227 => 550
  | 680778 => 563
  | 681342 => 196
  | _ => 0

private theorem part676539 : Segment Valid highEstimate e676539 e681539 := by
  apply gcd_batch (by decide) (by decide) extra676539 12
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [676539,681539). -/
theorem batch676539 :
    Segment Valid highEstimate
      ⟨676539, 676351726654129048, 676356818643495776, 907565785128918, 907577162104873⟩
      ⟨681539, 681474710851515516, 681479826622517843, 914278741120503, 914290154891211⟩ := by
  exact part676539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
