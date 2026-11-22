/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 911539 to 916539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e911539 : Edge :=
  ⟨911539, 911892214537799288, 911898596014063683, 1053082544590572, 1053095182829703⟩

private def e916539 : Edge :=
  ⟨916539, 916673325082273885, 916679743113070684, 1057657255195228, 1057669947687839⟩

private def extra911539 : ℕ → ℕ
  | 911539 => 363
  | 911903 => 383
  | 912287 => 361
  | 912649 => 389
  | 913039 => 531
  | 913571 => 721
  | 914293 => 603
  | 914897 => 689
  | 915587 => 631
  | 916219 => 319
  | _ => 0

private theorem part911539 : Segment Valid highEstimate e911539 e916539 := by
  apply gcd_batch (by decide) (by decide) extra911539 10
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [911539,916539). -/
theorem batch911539 :
    Segment Valid highEstimate
      ⟨911539, 911892214537799288, 911898596014063683, 1053082544590572, 1053095182829703⟩
      ⟨916539, 916673325082273885, 916679743113070684, 1057657255195228, 1057669947687839⟩ := by
  exact part911539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
