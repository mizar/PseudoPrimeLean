/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 366539 to 371539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e366539 : Edge :=
  ⟨366539, 366743271572259076, 366746166898606433, 678701384824462, 678709988403382⟩

private def e371539 : Edge :=
  ⟨371539, 371469470669330539, 371472400677136348, 687674857651619, 687683782233567⟩

private def extra366539 : ℕ → ℕ
  | 366539 => 319
  | 366859 => 267
  | 367127 => 263
  | 367391 => 271
  | 367663 => 219
  | 367883 => 257
  | 368141 => 269
  | 368411 => 305
  | 368717 => 353
  | 369071 => 397
  | 369469 => 491
  | 369961 => 478
  | 370440 => 448
  | 370889 => 448
  | 371338 => 200
  | _ => 0

private theorem part366539 : Segment Valid highEstimate e366539 e371539 := by
  apply gcd_batch (by decide) (by decide) extra366539 15
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [366539,371539). -/
theorem batch366539 :
    Segment Valid highEstimate
      ⟨366539, 366743271572259076, 366746166898606433, 678701384824462, 678709988403382⟩
      ⟨371539, 371469470669330539, 371472400677136348, 687674857651619, 687683782233567⟩ := by
  exact part366539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
