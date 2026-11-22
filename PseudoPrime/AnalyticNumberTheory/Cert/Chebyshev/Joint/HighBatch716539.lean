/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 716539 to 721539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e716539 : Edge :=
  ⟨716539, 716572739177339342, 716578109465859762, 942304906054199, 942316637549039⟩

private def e721539 : Edge :=
  ⟨721539, 721508536774991476, 721513970640436545, 942304906054199, 942316637549039⟩

private def extra716539 : ℕ → ℕ
  | 716539 => 609
  | 717149 => 701
  | 717851 => 652
  | 718504 => 579
  | 719084 => 526
  | 719611 => 484
  | 720096 => 512
  | 720609 => 512
  | 721122 => 416
  | _ => 0

private theorem part716539 : Segment Valid highEstimate e716539 e721539 := by
  apply gcd_batch (by decide) (by decide) extra716539 9
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [716539,721539). -/
theorem batch716539 :
    Segment Valid highEstimate
      ⟨716539, 716572739177339342, 716578109465859762, 942304906054199, 942316637549039⟩
      ⟨721539, 721508536774991476, 721513970640436545, 942304906054199, 942316637549039⟩ := by
  exact part716539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
