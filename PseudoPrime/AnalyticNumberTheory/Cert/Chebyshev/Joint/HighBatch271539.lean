/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 271539 to 276539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e271539 : Edge :=
  ⟨271539, 271636849207892232, 271638883120549580, 590982058712358, 590988903664281⟩

private def e276539 : Edge :=
  ⟨276539, 276639038602592967, 276641116711717283, 597241636923204, 597248712664322⟩

private def extra271539 : ℕ → ℕ
  | 271539 => 321
  | 271861 => 339
  | 272201 => 247
  | 272449 => 309
  | 272759 => 287
  | 273047 => 265
  | 273313 => 383
  | 273697 => 405
  | 274103 => 385
  | 274489 => 381
  | 274871 => 397
  | 275269 => 353
  | 275623 => 363
  | 275987 => 335
  | 276323 => 215
  | _ => 0

private theorem part271539 : Segment Valid highEstimate e271539 e276539 := by
  apply gcd_batch (by decide) (by decide) extra271539 15
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [271539,276539). -/
theorem batch271539 :
    Segment Valid highEstimate
      ⟨271539, 271636849207892232, 271638883120549580, 590982058712358, 590988903664281⟩
      ⟨276539, 276639038602592967, 276641116711717283, 597241636923204, 597248712664322⟩ := by
  exact part271539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
