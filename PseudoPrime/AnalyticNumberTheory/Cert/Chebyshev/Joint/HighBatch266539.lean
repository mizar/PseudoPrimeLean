/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 266539 to 271539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e266539 : Edge :=
  ⟨266539, 266454596163441081, 266456536110049775, 584726310457567, 584733000914240⟩

private def e271539 : Edge :=
  ⟨271539, 271636849207892232, 271638883120549580, 590982058712358, 590988903664281⟩

private def extra266539 : ℕ → ℕ
  | 266539 => 327
  | 266867 => 324
  | 267192 => 312
  | 267505 => 291
  | 267797 => 271
  | 268069 => 423
  | 268493 => 367
  | 268861 => 327
  | 269189 => 283
  | 269473 => 305
  | 269779 => 363
  | 270143 => 319
  | 270463 => 285
  | 270749 => 293
  | 271043 => 313
  | 271357 => 181
  | _ => 0

private theorem part266539 : Segment Valid highEstimate e266539 e271539 := by
  apply gcd_batch (by decide) (by decide) extra266539 16
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [266539,271539). -/
theorem batch266539 :
    Segment Valid highEstimate
      ⟨266539, 266454596163441081, 266456536110049775, 584726310457567, 584733000914240⟩
      ⟨271539, 271636849207892232, 271638883120549580, 590982058712358, 590988903664281⟩ := by
  exact part266539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
