/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 321539 to 326539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e321539 : Edge :=
  ⟨321539, 321593397510605728, 321595949965862868, 629835526100654, 629843334818269⟩

private def e326539 : Edge :=
  ⟨326539, 326618065632642258, 326620662106426693, 642526791887481, 642534922671444⟩

private def extra321539 : ℕ → ℕ
  | 321539 => 371
  | 321911 => 337
  | 322249 => 341
  | 322591 => 371
  | 322963 => 407
  | 323371 => 425
  | 323797 => 425
  | 324223 => 413
  | 324637 => 359
  | 324997 => 321
  | 325319 => 347
  | 325667 => 283
  | 325951 => 251
  | 326203 => 335
  | _ => 0

private theorem part321539 : Segment Valid highEstimate e321539 e326539 := by
  apply gcd_batch (by decide) (by decide) extra321539 14
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [321539,326539). -/
theorem batch321539 :
    Segment Valid highEstimate
      ⟨321539, 321593397510605728, 321595949965862868, 629835526100654, 629843334818269⟩
      ⟨326539, 326618065632642258, 326620662106426693, 642526791887481, 642534922671444⟩ := by
  exact part321539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
