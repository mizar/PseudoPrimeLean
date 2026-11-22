/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 336539 to 341539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e336539 : Edge :=
  ⟨336539, 336666324708878478, 336669015912378774, 648884634152238, 648892766443253⟩

private def e341539 : Edge :=
  ⟨341539, 341645214124329997, 341647926002239681, 648884634152238, 648892766443253⟩

private def extra336539 : ℕ → ℕ
  | 336539 => 283
  | 336823 => 257
  | 337081 => 261
  | 337343 => 283
  | 337627 => 245
  | 337873 => 293
  | 338167 => 201
  | 338369 => 197
  | 338567 => 205
  | 338773 => 293
  | 339067 => 273
  | 339341 => 331
  | 339673 => 383
  | 340057 => 389
  | 340447 => 371
  | 340819 => 359
  | 341179 => 341
  | 341521 => 17
  | _ => 0

private theorem part336539 : Segment Valid highEstimate e336539 e341539 := by
  apply gcd_batch (by decide) (by decide) extra336539 18
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [336539,341539). -/
theorem batch336539 :
    Segment Valid highEstimate
      ⟨336539, 336666324708878478, 336669015912378774, 648884634152238, 648892766443253⟩
      ⟨341539, 341645214124329997, 341647926002239681, 648884634152238, 648892766443253⟩ := by
  exact part336539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
