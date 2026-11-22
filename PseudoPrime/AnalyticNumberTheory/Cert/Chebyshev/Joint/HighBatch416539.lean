/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 416539 to 421539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e416539 : Edge :=
  ⟨416539, 416438995831443231, 416442194748141419, 732222569694224, 732231972890661⟩

private def e421539 : Edge :=
  ⟨421539, 421416649240886826, 421419867687234253, 738694915556115, 738704378567016⟩

private def extra416539 : ℕ → ℕ
  | 416539 => 415
  | 416955 => 284
  | 417240 => 310
  | 417551 => 297
  | 417849 => 322
  | 418172 => 349
  | 418522 => 375
  | 418898 => 419
  | 419318 => 414
  | 419733 => 440
  | 420174 => 374
  | 420549 => 414
  | 420964 => 388
  | 421353 => 185
  | _ => 0

private theorem part416539 : Segment Valid highEstimate e416539 e421539 := by
  apply gcd_batch (by decide) (by decide) extra416539 14
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [416539,421539). -/
theorem batch416539 :
    Segment Valid highEstimate
      ⟨416539, 416438995831443231, 416442194748141419, 732222569694224, 732231972890661⟩
      ⟨421539, 421416649240886826, 421419867687234253, 738694915556115, 738704378567016⟩ := by
  exact part416539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
