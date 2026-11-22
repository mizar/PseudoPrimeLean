/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 331539 to 336539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e331539 : Edge :=
  ⟨331539, 331725008061551196, 331727639643786108, 642526791887481, 642534922671444⟩

private def e336539 : Edge :=
  ⟨336539, 336666324708878478, 336669015912378774, 648884634152238, 648892766443253⟩

private def extra331539 : ℕ → ℕ
  | 331539 => 261
  | 331801 => 251
  | 332053 => 219
  | 332273 => 239
  | 332513 => 323
  | 332837 => 301
  | 333139 => 293
  | 333433 => 267
  | 333701 => 295
  | 333997 => 333
  | 334331 => 319
  | 334651 => 321
  | 334973 => 275
  | 335249 => 289
  | 335539 => 293
  | 335833 => 323
  | 336157 => 363
  | 336521 => 17
  | _ => 0

private theorem part331539 : Segment Valid highEstimate e331539 e336539 := by
  apply gcd_batch (by decide) (by decide) extra331539 18
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [331539,336539). -/
theorem batch331539 :
    Segment Valid highEstimate
      ⟨331539, 331725008061551196, 331727639643786108, 642526791887481, 642534922671444⟩
      ⟨336539, 336666324708878478, 336669015912378774, 648884634152238, 648892766443253⟩ := by
  exact part331539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
