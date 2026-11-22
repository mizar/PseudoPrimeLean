/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 796539 to 801539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e796539 : Edge :=
  ⟨796539, 796625522429139383, 796631368640420656, 996452017626611, 996464214691058⟩

private def e801539 : Edge :=
  ⟨801539, 801722201739233966, 801728096680372869, 996452017626611, 996464214691058⟩

private def extra796539 : ℕ → ℕ
  | 796539 => 499
  | 797039 => 539
  | 797579 => 551
  | 798131 => 535
  | 798667 => 645
  | 799313 => 647
  | 799961 => 571
  | 800533 => 467
  | 801001 => 515
  | 801517 => 21
  | _ => 0

private theorem part796539 : Segment Valid highEstimate e796539 e801539 := by
  apply gcd_batch (by decide) (by decide) extra796539 10
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [796539,801539). -/
theorem batch796539 :
    Segment Valid highEstimate
      ⟨796539, 796625522429139383, 796631368640420656, 996452017626611, 996464214691058⟩
      ⟨801539, 801722201739233966, 801728096680372869, 996452017626611, 996464214691058⟩ := by
  exact part796539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
