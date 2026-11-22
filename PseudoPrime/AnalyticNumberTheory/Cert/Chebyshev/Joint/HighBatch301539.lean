/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 301539 to 306539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e301539 : Edge :=
  ⟨301539, 301278727200321726, 301281083501084600, 617179685752607, 617187194586000⟩

private def e306539 : Edge :=
  ⟨306539, 306454995417763145, 306457397240772409, 617179685752607, 617187194586000⟩

private def extra301539 : ℕ → ℕ
  | 301539 => 178
  | 301718 => 188
  | 301907 => 188
  | 302096 => 151
  | 302248 => 138
  | 302387 => 100
  | 302488 => 87
  | 302576 => 75
  | 302652 => 100
  | 302753 => 62
  | 302816 => 62
  | 302879 => 88
  | 302968 => 87
  | 303056 => 163
  | 303220 => 138
  | 303359 => 138
  | 303498 => 189
  | 303688 => 214
  | 303903 => 201
  | 304105 => 239
  | 304345 => 188
  | 304534 => 252
  | 304787 => 264
  | 305052 => 328
  | 305381 => 302
  | 305684 => 340
  | 306025 => 315
  | 306341 => 197
  | _ => 0

private theorem part301539 : Segment Valid highEstimate e301539 e306539 := by
  apply gcd_batch (by decide) (by decide) extra301539 28
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [301539,306539). -/
theorem batch301539 :
    Segment Valid highEstimate
      ⟨301539, 301278727200321726, 301281083501084600, 617179685752607, 617187194586000⟩
      ⟨306539, 306454995417763145, 306457397240772409, 617179685752607, 617187194586000⟩ := by
  exact part301539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
