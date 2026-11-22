/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 721539 to 726539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e721539 : Edge :=
  ⟨721539, 721508536774991476, 721513970640436545, 942304906054199, 942316637549039⟩

private def e726539 : Edge :=
  ⟨726539, 726568256142213967, 726573694285358171, 942304906054199, 942316637549039⟩

private def extra721539 : ℕ → ℕ
  | 721539 => 648
  | 722188 => 633
  | 722822 => 620
  | 723443 => 635
  | 724079 => 571
  | 724651 => 641
  | 725293 => 687
  | 725981 => 557
  | _ => 0

private theorem part721539 : Segment Valid highEstimate e721539 e726539 := by
  apply gcd_batch (by decide) (by decide) extra721539 8
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [721539,726539). -/
theorem batch721539 :
    Segment Valid highEstimate
      ⟨721539, 721508536774991476, 721513970640436545, 942304906054199, 942316637549039⟩
      ⟨726539, 726568256142213967, 726573694285358171, 942304906054199, 942316637549039⟩ := by
  exact part721539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
