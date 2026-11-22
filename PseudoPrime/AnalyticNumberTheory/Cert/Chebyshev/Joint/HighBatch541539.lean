/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 541539 to 546539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e541539 : Edge :=
  ⟨541539, 541577557633886101, 541581396707376733, 823296512632682, 823307116887428⟩

private def e546539 : Edge :=
  ⟨546539, 546497036782029497, 546500884131748939, 829901810531116, 829912423093115⟩

private def extra541539 : ℕ → ℕ
  | 541539 => 531
  | 542071 => 485
  | 542557 => 539
  | 543097 => 503
  | 543601 => 407
  | 544009 => 507
  | 544517 => 545
  | 545063 => 587
  | 545651 => 587
  | 546239 => 299
  | _ => 0

private theorem part541539 : Segment Valid highEstimate e541539 e546539 := by
  apply gcd_batch (by decide) (by decide) extra541539 10
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [541539,546539). -/
theorem batch541539 :
    Segment Valid highEstimate
      ⟨541539, 541577557633886101, 541581396707376733, 823296512632682, 823307116887428⟩
      ⟨546539, 546497036782029497, 546500884131748939, 829901810531116, 829912423093115⟩ := by
  exact part541539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
