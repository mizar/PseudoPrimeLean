/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 551539 to 556539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e551539 : Edge :=
  ⟨551539, 551519086700785211, 551522980868759895, 829901810531116, 829912423093115⟩

private def e556539 : Edge :=
  ⟨556539, 556405675189643609, 556409682461398322, 836512506291081, 836523164081411⟩

private def extra551539 : ℕ → ℕ
  | 551539 => 549
  | 552089 => 619
  | 552709 => 574
  | 553284 => 564
  | 553849 => 597
  | 554447 => 529
  | 554977 => 659
  | 555637 => 530
  | 556168 => 370
  | _ => 0

private theorem part551539 : Segment Valid highEstimate e551539 e556539 := by
  apply gcd_batch (by decide) (by decide) extra551539 9
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [551539,556539). -/
theorem batch551539 :
    Segment Valid highEstimate
      ⟨551539, 551519086700785211, 551522980868759895, 829901810531116, 829912423093115⟩
      ⟨556539, 556405675189643609, 556409682461398322, 836512506291081, 836523164081411⟩ := by
  exact part551539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
