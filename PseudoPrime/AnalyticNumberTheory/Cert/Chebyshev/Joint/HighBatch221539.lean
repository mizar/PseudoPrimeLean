/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 221539 to 226539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e221539 : Edge :=
  ⟨221539, 221562348463509236, 221564110857657096, 542700239780932, 542706527944601⟩

private def e226539 : Edge :=
  ⟨226539, 226564048406585613, 226565830273712052, 542700239780932, 542706527944601⟩

private def extra221539 : ℕ → ℕ
  | 221539 => 333
  | 221873 => 289
  | 222163 => 335
  | 222499 => 363
  | 222863 => 355
  | 223219 => 287
  | 223507 => 329
  | 223837 => 359
  | 224197 => 329
  | 224527 => 363
  | 224891 => 331
  | 225223 => 303
  | 225527 => 301
  | 225829 => 311
  | 226141 => 341
  | 226483 => 55
  | _ => 0

private theorem part221539 : Segment Valid highEstimate e221539 e226539 := by
  apply gcd_batch (by decide) (by decide) extra221539 16
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [221539,226539). -/
theorem batch221539 :
    Segment Valid highEstimate
      ⟨221539, 221562348463509236, 221564110857657096, 542700239780932, 542706527944601⟩
      ⟨226539, 226564048406585613, 226565830273712052, 542700239780932, 542706527944601⟩ := by
  exact part221539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
