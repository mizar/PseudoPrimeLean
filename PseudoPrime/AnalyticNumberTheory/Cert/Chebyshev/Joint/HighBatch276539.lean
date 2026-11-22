/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 276539 to 281539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e276539 : Edge :=
  ⟨276539, 276639038602592967, 276641116711717283, 597241636923204, 597248712664322⟩

private def e281539 : Edge :=
  ⟨281539, 281532440907291208, 281534577313136198, 600377131139129, 600384206880252⟩

private def extra276539 : ℕ → ℕ
  | 276539 => 307
  | 276847 => 335
  | 277183 => 365
  | 277549 => 353
  | 277903 => 375
  | 278279 => 371
  | 278651 => 371
  | 279023 => 427
  | 279451 => 418
  | 279870 => 416
  | 280287 => 401
  | 280689 => 379
  | 281069 => 361
  | 281431 => 107
  | _ => 0

private theorem part276539 : Segment Valid highEstimate e276539 e281539 := by
  apply gcd_batch (by decide) (by decide) extra276539 14
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [276539,281539). -/
theorem batch276539 :
    Segment Valid highEstimate
      ⟨276539, 276639038602592967, 276641116711717283, 597241636923204, 597248712664322⟩
      ⟨281539, 281532440907291208, 281534577313136198, 600377131139129, 600384206880252⟩ := by
  exact part276539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
