/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 961539 to 966539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e961539 : Edge :=
  ⟨961539, 961392508433358735, 961399078287689346, 1081728253389386, 1081741038637830⟩

private def e966539 : Edge :=
  ⟨966539, 966566468497449366, 966573077998451939, 1088618862387204, 1088631673355392⟩

private def extra961539 : ℕ → ℕ
  | 961539 => 637
  | 962177 => 757
  | 962935 => 757
  | 963693 => 729
  | 964423 => 765
  | 965189 => 805
  | 965995 => 543
  | _ => 0

private theorem part961539 : Segment Valid highEstimate e961539 e966539 := by
  apply gcd_batch (by decide) (by decide) extra961539 7
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [961539,966539). -/
theorem batch961539 :
    Segment Valid highEstimate
      ⟨961539, 961392508433358735, 961399078287689346, 1081728253389386, 1081741038637830⟩
      ⟨966539, 966566468497449366, 966573077998451939, 1088618862387204, 1088631673355392⟩ := by
  exact part961539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
