/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 356539 to 361539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e356539 : Edge :=
  ⟨356539, 356781923285159961, 356784746846589057, 661644851080582, 661653167150248⟩

private def e361539 : Edge :=
  ⟨361539, 361621228998278365, 361624100837074789, 678701384824462, 678709988403382⟩

private def extra356539 : ℕ → ℕ
  | 356539 => 291
  | 356831 => 299
  | 357131 => 305
  | 357437 => 251
  | 357689 => 277
  | 357967 => 305
  | 358273 => 297
  | 358571 => 239
  | 358811 => 191
  | 359003 => 203
  | 359207 => 181
  | 359389 => 173
  | 359563 => 183
  | 359747 => 289
  | 360037 => 269
  | 360307 => 461
  | 360769 => 449
  | 361219 => 319
  | _ => 0

private theorem part356539 : Segment Valid highEstimate e356539 e361539 := by
  apply gcd_batch (by decide) (by decide) extra356539 18
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [356539,361539). -/
theorem batch356539 :
    Segment Valid highEstimate
      ⟨356539, 356781923285159961, 356784746846589057, 661644851080582, 661653167150248⟩
      ⟨361539, 361621228998278365, 361624100837074789, 678701384824462, 678709988403382⟩ := by
  exact part356539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
