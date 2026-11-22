/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 886539 to 891539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e886539 : Edge :=
  ⟨886539, 886818139254799858, 886824436236879330, 1039369630891237, 1039382218633003⟩

private def e891539 : Edge :=
  ⟨891539, 891694581140459969, 891700882763878255, 1039369630891237, 1039382218633003⟩

private def extra886539 : ℕ → ℕ
  | 886539 => 477
  | 887017 => 549
  | 887567 => 493
  | 888061 => 437
  | 888499 => 461
  | 888961 => 429
  | 889391 => 515
  | 889907 => 559
  | 890467 => 581
  | 891049 => 489
  | _ => 0

private theorem part886539 : Segment Valid highEstimate e886539 e891539 := by
  apply gcd_batch (by decide) (by decide) extra886539 10
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [886539,891539). -/
theorem batch886539 :
    Segment Valid highEstimate
      ⟨886539, 886818139254799858, 886824436236879330, 1039369630891237, 1039382218633003⟩
      ⟨891539, 891694581140459969, 891700882763878255, 1039369630891237, 1039382218633003⟩ := by
  exact part886539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
