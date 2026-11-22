/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 881539 to 886539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e881539 : Edge :=
  ⟨881539, 881909430338492309, 881915694672363901, 1032522688658498, 1032535178279526⟩

private def e886539 : Edge :=
  ⟨886539, 886818139254799858, 886824436236879330, 1039369630891237, 1039382218633003⟩

private def extra881539 : ℕ → ℕ
  | 881539 => 489
  | 882029 => 499
  | 882529 => 531
  | 883061 => 475
  | 883537 => 519
  | 884057 => 479
  | 884537 => 569
  | 885107 => 605
  | 885713 => 485
  | 886199 => 339
  | _ => 0

private theorem part881539 : Segment Valid highEstimate e881539 e886539 := by
  apply gcd_batch (by decide) (by decide) extra881539 10
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [881539,886539). -/
theorem batch881539 :
    Segment Valid highEstimate
      ⟨881539, 881909430338492309, 881915694672363901, 1032522688658498, 1032535178279526⟩
      ⟨886539, 886818139254799858, 886824436236879330, 1039369630891237, 1039382218633003⟩ := by
  exact part881539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
