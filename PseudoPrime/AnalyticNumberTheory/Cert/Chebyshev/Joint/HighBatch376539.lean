/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 376539 to 381539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e376539 : Edge :=
  ⟨376539, 376493265700140190, 376496240883480121, 694093222403295, 694102180799745⟩

private def e381539 : Edge :=
  ⟨381539, 381509390752494752, 381512382359236606, 700518090357880, 700527158313291⟩

private def extra376539 : ℕ → ℕ
  | 376539 => 429
  | 376969 => 521
  | 377491 => 468
  | 377960 => 436
  | 378397 => 411
  | 378809 => 423
  | 379233 => 449
  | 379683 => 461
  | 380145 => 449
  | 380595 => 449
  | 381045 => 430
  | 381476 => 62
  | _ => 0

private theorem part376539 : Segment Valid highEstimate e376539 e381539 := by
  apply gcd_batch (by decide) (by decide) extra376539 12
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [376539,381539). -/
theorem batch376539 :
    Segment Valid highEstimate
      ⟨376539, 376493265700140190, 376496240883480121, 694093222403295, 694102180799745⟩
      ⟨381539, 381509390752494752, 381512382359236606, 700518090357880, 700527158313291⟩ := by
  exact part376539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
