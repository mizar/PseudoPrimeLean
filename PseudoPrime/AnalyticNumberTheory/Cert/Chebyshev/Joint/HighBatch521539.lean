/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 521539 to 526539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e521539 : Edge :=
  ⟨521539, 521708485598715597, 521712107609132688, 808318683224023, 808329077216397⟩

private def e526539 : Edge :=
  ⟨526539, 526766214191606998, 526769855324902447, 809011830404582, 809022224396958⟩

private def extra521539 : ℕ → ℕ
  | 521539 => 357
  | 521897 => 353
  | 522251 => 385
  | 522637 => 323
  | 522961 => 455
  | 523417 => 411
  | 523829 => 401
  | 524231 => 475
  | 524707 => 449
  | 525157 => 383
  | 525541 => 395
  | 525937 => 351
  | 526289 => 249
  | _ => 0

private theorem part521539 : Segment Valid highEstimate e521539 e526539 := by
  apply gcd_batch (by decide) (by decide) extra521539 13
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [521539,526539). -/
theorem batch521539 :
    Segment Valid highEstimate
      ⟨521539, 521708485598715597, 521712107609132688, 808318683224023, 808329077216397⟩
      ⟨526539, 526766214191606998, 526769855324902447, 809011830404582, 809022224396958⟩ := by
  exact part521539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
