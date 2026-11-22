/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 836539 to 841539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e836539 : Edge :=
  ⟨836539, 836744205537533115, 836750279065628673, 1012022610967268, 1012035023523210⟩

private def e841539 : Edge :=
  ⟨841539, 841613699477514666, 841619776629808475, 1012022610967268, 1012035023523210⟩

private def extra836539 : ℕ → ℕ
  | 836539 => 531
  | 837071 => 595
  | 837667 => 683
  | 838351 => 587
  | 838939 => 659
  | 839599 => 639
  | 840239 => 683
  | 840923 => 615
  | _ => 0

private theorem part836539 : Segment Valid highEstimate e836539 e841539 := by
  apply gcd_batch (by decide) (by decide) extra836539 8
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [836539,841539). -/
theorem batch836539 :
    Segment Valid highEstimate
      ⟨836539, 836744205537533115, 836750279065628673, 1012022610967268, 1012035023523210⟩
      ⟨841539, 841613699477514666, 841619776629808475, 1012022610967268, 1012035023523210⟩ := by
  exact part836539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
