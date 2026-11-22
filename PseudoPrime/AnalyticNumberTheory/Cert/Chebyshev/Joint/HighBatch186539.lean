/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 186539 to 191539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e186539 : Edge :=
  ⟨186539, 186559095622921103, 186560655391780817, 489724738027783, 489730665251735⟩

private def e191539 : Edge :=
  ⟨191539, 191558662826644864, 191560257013900818, 495795475751650, 495801405654795⟩

private def extra186539 : ℕ → ℕ
  | 186539 => 301
  | 186841 => 297
  | 187139 => 269
  | 187409 => 251
  | 187661 => 269
  | 187931 => 359
  | 188291 => 331
  | 188623 => 315
  | 188939 => 331
  | 189271 => 287
  | 189559 => 293
  | 189853 => 293
  | 190147 => 375
  | 190523 => 305
  | 190829 => 313
  | 191143 => 363
  | 191507 => 31
  | _ => 0

private theorem part186539 : Segment Valid highEstimate e186539 e191539 := by
  apply gcd_batch (by decide) (by decide) extra186539 17
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [186539,191539). -/
theorem batch186539 :
    Segment Valid highEstimate
      ⟨186539, 186559095622921103, 186560655391780817, 489724738027783, 489730665251735⟩
      ⟨191539, 191558662826644864, 191560257013900818, 495795475751650, 495801405654795⟩ := by
  exact part186539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
