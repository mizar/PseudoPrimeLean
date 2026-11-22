/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 636539 to 641539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e636539 : Edge :=
  ⟨636539, 636589465506940966, 636594243338504390, 887461196452993, 887472396843589⟩

private def e641539 : Edge :=
  ⟨641539, 641335004472386096, 641339831537883740, 887461196452993, 887472396843589⟩

private def extra636539 : ℕ → ℕ
  | 636539 => 599
  | 637139 => 559
  | 637699 => 627
  | 638327 => 651
  | 638979 => 481
  | 639461 => 440
  | 639902 => 440
  | 640343 => 521
  | 640865 => 441
  | 641307 => 231
  | _ => 0

private theorem part636539 : Segment Valid highEstimate e636539 e641539 := by
  apply gcd_batch (by decide) (by decide) extra636539 10
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [636539,641539). -/
theorem batch636539 :
    Segment Valid highEstimate
      ⟨636539, 636589465506940966, 636594243338504390, 887461196452993, 887472396843589⟩
      ⟨641539, 641335004472386096, 641339831537883740, 887461196452993, 887472396843589⟩ := by
  exact part636539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
