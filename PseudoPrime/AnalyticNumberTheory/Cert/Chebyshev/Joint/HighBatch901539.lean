/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 901539 to 906539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e901539 : Edge :=
  ⟨901539, 901720685380952995, 901727049257808867, 1046222929973740, 1046235522765251⟩

private def e906539 : Edge :=
  ⟨906539, 906603126071419620, 906609492378114731, 1046222929973740, 1046235522765251⟩

private def extra901539 : ℕ → ℕ
  | 901539 => 651
  | 902191 => 657
  | 902849 => 719
  | 903569 => 799
  | 904369 => 717
  | 905087 => 695
  | 905783 => 697
  | 906481 => 57
  | _ => 0

private theorem part901539 : Segment Valid highEstimate e901539 e906539 := by
  apply gcd_batch (by decide) (by decide) extra901539 8
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [901539,906539). -/
theorem batch901539 :
    Segment Valid highEstimate
      ⟨901539, 901720685380952995, 901727049257808867, 1046222929973740, 1046235522765251⟩
      ⟨906539, 906603126071419620, 906609492378114731, 1046222929973740, 1046235522765251⟩ := by
  exact part901539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
