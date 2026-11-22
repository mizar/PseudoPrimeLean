/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 981539 to 986539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e981539 : Edge :=
  ⟨981539, 981348438476331104, 981355090621901309, 1088618862387204, 1088631673355392⟩

private def e986539 : Edge :=
  ⟨986539, 986240342261767815, 986247008254562085, 1095517575725254, 1095530504794266⟩

private def extra981539 : ℕ → ℕ
  | 981539 => 601
  | 982141 => 585
  | 982727 => 524
  | 983252 => 537
  | 983790 => 510
  | 984301 => 455
  | 984757 => 523
  | 985281 => 455
  | 985737 => 496
  | 986234 => 304
  | _ => 0

private theorem part981539 : Segment Valid highEstimate e981539 e986539 := by
  apply gcd_batch (by decide) (by decide) extra981539 10
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [981539,986539). -/
theorem batch981539 :
    Segment Valid highEstimate
      ⟨981539, 981348438476331104, 981355090621901309, 1088618862387204, 1088631673355392⟩
      ⟨986539, 986240342261767815, 986247008254562085, 1095517575725254, 1095530504794266⟩ := by
  exact part981539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
