/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 986539 to 991539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e986539 : Edge :=
  ⟨986539, 986240342261767815, 986247008254562085, 1095517575725254, 1095530504794266⟩

private def e991539 : Edge :=
  ⟨991539, 991140935656725200, 991147608655976359, 1095517575725254, 1095530504794266⟩

private def extra986539 : ℕ → ℕ
  | 986539 => 495
  | 987035 => 579
  | 987615 => 537
  | 988153 => 455
  | 988609 => 468
  | 989078 => 400
  | 989479 => 385
  | 989865 => 359
  | 990225 => 371
  | 990597 => 441
  | 991039 => 414
  | 991454 => 84
  | _ => 0

private theorem part986539 : Segment Valid highEstimate e986539 e991539 := by
  apply gcd_batch (by decide) (by decide) extra986539 12
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [986539,991539). -/
theorem batch986539 :
    Segment Valid highEstimate
      ⟨986539, 986240342261767815, 986247008254562085, 1095517575725254, 1095530504794266⟩
      ⟨991539, 991140935656725200, 991147608655976359, 1095517575725254, 1095530504794266⟩ := by
  exact part986539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
