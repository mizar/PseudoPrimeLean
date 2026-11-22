/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 371539 to 376539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e371539 : Edge :=
  ⟨371539, 371469470669330539, 371472400677136348, 687674857651619, 687683782233567⟩

private def e376539 : Edge :=
  ⟨376539, 376493265700140190, 376496240883480121, 694093222403295, 694102180799745⟩

private def extra371539 : ℕ → ℕ
  | 371539 => 417
  | 371957 => 371
  | 372329 => 371
  | 372701 => 346
  | 373048 => 397
  | 373446 => 397
  | 373844 => 345
  | 374190 => 398
  | 374589 => 320
  | 374910 => 384
  | 375295 => 465
  | 375761 => 475
  | 376237 => 301
  | _ => 0

private theorem part371539 : Segment Valid highEstimate e371539 e376539 := by
  apply gcd_batch (by decide) (by decide) extra371539 13
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [371539,376539). -/
theorem batch371539 :
    Segment Valid highEstimate
      ⟨371539, 371469470669330539, 371472400677136348, 687674857651619, 687683782233567⟩
      ⟨376539, 376493265700140190, 376496240883480121, 694093222403295, 694102180799745⟩ := by
  exact part371539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
