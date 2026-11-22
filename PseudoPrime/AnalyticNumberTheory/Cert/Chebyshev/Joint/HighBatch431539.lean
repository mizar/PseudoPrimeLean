/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 431539 to 436539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e431539 : Edge :=
  ⟨431539, 431443924113567568, 431447191929929561, 745176489933631, 745186159243371⟩

private def e436539 : Edge :=
  ⟨436539, 436733609062523898, 436736905534581059, 751667213436352, 751676893203048⟩

private def extra431539 : ℕ → ℕ
  | 431539 => 429
  | 431969 => 454
  | 432424 => 506
  | 432931 => 437
  | 433369 => 443
  | 433813 => 453
  | 434267 => 449
  | 434717 => 413
  | 435131 => 349
  | 435481 => 287
  | 435769 => 317
  | 436087 => 351
  | 436439 => 99
  | _ => 0

private theorem part431539 : Segment Valid highEstimate e431539 e436539 := by
  apply gcd_batch (by decide) (by decide) extra431539 13
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [431539,436539). -/
theorem batch431539 :
    Segment Valid highEstimate
      ⟨431539, 431443924113567568, 431447191929929561, 745176489933631, 745186159243371⟩
      ⟨436539, 436733609062523898, 436736905534581059, 751667213436352, 751676893203048⟩ := by
  exact part431539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
