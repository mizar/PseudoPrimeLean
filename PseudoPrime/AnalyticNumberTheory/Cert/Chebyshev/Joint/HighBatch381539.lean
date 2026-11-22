/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 381539 to 386539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e381539 : Edge :=
  ⟨381539, 381509390752494752, 381512382359236606, 700518090357880, 700527158313291⟩

private def e386539 : Edge :=
  ⟨386539, 386530700350060504, 386533732838157433, 706946193682963, 706955425300522⟩

private def extra381539 : ℕ → ℕ
  | 381539 => 463
  | 382003 => 424
  | 382428 => 320
  | 382749 => 347
  | 383097 => 372
  | 383470 => 339
  | 383810 => 385
  | 384196 => 424
  | 384621 => 450
  | 385072 => 410
  | 385483 => 424
  | 385908 => 450
  | 386359 => 179
  | _ => 0

private theorem part381539 : Segment Valid highEstimate e381539 e386539 := by
  apply gcd_batch (by decide) (by decide) extra381539 13
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [381539,386539). -/
theorem batch381539 :
    Segment Valid highEstimate
      ⟨381539, 381509390752494752, 381512382359236606, 700518090357880, 700527158313291⟩
      ⟨386539, 386530700350060504, 386533732838157433, 706946193682963, 706955425300522⟩ := by
  exact part381539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
