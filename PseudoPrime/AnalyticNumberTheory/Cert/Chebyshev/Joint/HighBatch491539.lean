/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 491539 to 496539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e491539 : Edge :=
  ⟨491539, 491558605298468616, 491562135455576305, 790807522475477, 790817582073658⟩

private def e496539 : Edge :=
  ⟨496539, 496649842794941820, 496653379998464633, 795176969632206, 795187111413169⟩

private def extra491539 : ℕ → ℕ
  | 491539 => 521
  | 492061 => 608
  | 492670 => 497
  | 493168 => 502
  | 493671 => 511
  | 494183 => 523
  | 494707 => 561
  | 495269 => 443
  | 495713 => 449
  | 496163 => 375
  | _ => 0

private theorem part491539 : Segment Valid highEstimate e491539 e496539 := by
  apply gcd_batch (by decide) (by decide) extra491539 10
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [491539,496539). -/
theorem batch491539 :
    Segment Valid highEstimate
      ⟨491539, 491558605298468616, 491562135455576305, 790807522475477, 790817582073658⟩
      ⟨496539, 496649842794941820, 496653379998464633, 795176969632206, 795187111413169⟩ := by
  exact part491539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
