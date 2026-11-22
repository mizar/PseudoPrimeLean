/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 516539 to 521539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e516539 : Edge :=
  ⟨516539, 516490684436095305, 516494298335432352, 801740825039943, 801750992042056⟩

private def e521539 : Edge :=
  ⟨521539, 521708485598715597, 521712107609132688, 808318683224023, 808329077216397⟩

private def extra516539 : ℕ → ℕ
  | 516539 => 539
  | 517079 => 433
  | 517513 => 467
  | 517981 => 447
  | 518429 => 433
  | 518863 => 443
  | 519307 => 429
  | 519737 => 455
  | 520193 => 439
  | 520633 => 429
  | 521063 => 433
  | 521497 => 41
  | _ => 0

private theorem part516539 : Segment Valid highEstimate e516539 e521539 := by
  apply gcd_batch (by decide) (by decide) extra516539 12
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [516539,521539). -/
theorem batch516539 :
    Segment Valid highEstimate
      ⟨516539, 516490684436095305, 516494298335432352, 801740825039943, 801750992042056⟩
      ⟨521539, 521708485598715597, 521712107609132688, 808318683224023, 808329077216397⟩ := by
  exact part516539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
