/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 621539 to 626539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e621539 : Edge :=
  ⟨621539, 621815422073023980, 621820085293590167, 880780343275270, 880791406190584⟩

private def e626539 : Edge :=
  ⟨626539, 626619218107783773, 626623909829185081, 880780343275270, 880791406190584⟩

private def extra621539 : ℕ → ℕ
  | 621539 => 373
  | 621913 => 335
  | 622249 => 357
  | 622607 => 395
  | 623003 => 413
  | 623417 => 449
  | 623867 => 373
  | 624241 => 357
  | 624599 => 373
  | 624973 => 369
  | 625343 => 433
  | 625777 => 461
  | 626239 => 299
  | _ => 0

private theorem part621539 : Segment Valid highEstimate e621539 e626539 := by
  apply gcd_batch (by decide) (by decide) extra621539 13
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [621539,626539). -/
theorem batch621539 :
    Segment Valid highEstimate
      ⟨621539, 621815422073023980, 621820085293590167, 880780343275270, 880791406190584⟩
      ⟨626539, 626619218107783773, 626623909829185081, 880780343275270, 880791406190584⟩ := by
  exact part621539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
