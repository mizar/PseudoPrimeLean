/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 411539 to 416539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e411539 : Edge :=
  ⟨411539, 411349557745615430, 411352730760635390, 725756425004208, 725765817214306⟩

private def e416539 : Edge :=
  ⟨416539, 416438995831443231, 416442194748141419, 732222569694224, 732231972890661⟩

private def extra411539 : ℕ → ℕ
  | 411539 => 322
  | 411862 => 388
  | 412251 => 451
  | 412703 => 400
  | 413104 => 336
  | 413441 => 284
  | 413726 => 264
  | 413991 => 219
  | 414211 => 245
  | 414457 => 283
  | 414741 => 349
  | 415091 => 374
  | 415466 => 323
  | 415790 => 387
  | 416178 => 360
  | _ => 0

private theorem part411539 : Segment Valid highEstimate e411539 e416539 := by
  apply gcd_batch (by decide) (by decide) extra411539 15
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [411539,416539). -/
theorem batch411539 :
    Segment Valid highEstimate
      ⟨411539, 411349557745615430, 411352730760635390, 725756425004208, 725765817214306⟩
      ⟨416539, 416438995831443231, 416442194748141419, 732222569694224, 732231972890661⟩ := by
  exact part411539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
