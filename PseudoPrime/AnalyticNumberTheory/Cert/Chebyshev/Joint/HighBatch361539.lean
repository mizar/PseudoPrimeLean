/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 361539 to 366539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e361539 : Edge :=
  ⟨361539, 361621228998278365, 361624100837074789, 678701384824462, 678709988403382⟩

private def e366539 : Edge :=
  ⟨366539, 366743271572259076, 366746166898606433, 678701384824462, 678709988403382⟩

private def extra361539 : ℕ → ℕ
  | 361539 => 403
  | 361943 => 389
  | 362333 => 409
  | 362743 => 429
  | 363173 => 377
  | 363551 => 365
  | 363917 => 385
  | 364303 => 353
  | 364657 => 359
  | 365017 => 359
  | 365377 => 305
  | 365683 => 347
  | 366031 => 297
  | 366329 => 209
  | _ => 0

private theorem part361539 : Segment Valid highEstimate e361539 e366539 := by
  apply gcd_batch (by decide) (by decide) extra361539 14
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [361539,366539). -/
theorem batch361539 :
    Segment Valid highEstimate
      ⟨361539, 361621228998278365, 361624100837074789, 678701384824462, 678709988403382⟩
      ⟨366539, 366743271572259076, 366746166898606433, 678701384824462, 678709988403382⟩ := by
  exact part361539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
