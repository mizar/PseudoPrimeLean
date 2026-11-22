/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 281539 to 286539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e281539 : Edge :=
  ⟨281539, 281532440907291208, 281534577313136198, 600377131139129, 600384206880252⟩

private def e286539 : Edge :=
  ⟨286539, 286555084003313897, 286557302212596025, 600377131139129, 600384206880252⟩

private def extra281539 : ℕ → ℕ
  | 281539 => 317
  | 281857 => 285
  | 282143 => 295
  | 282439 => 329
  | 282769 => 329
  | 283099 => 411
  | 283511 => 425
  | 283937 => 403
  | 284341 => 359
  | 284701 => 305
  | 285007 => 293
  | 285301 => 329
  | 285631 => 347
  | 285979 => 447
  | 286427 => 111
  | _ => 0

private theorem part281539 : Segment Valid highEstimate e281539 e286539 := by
  apply gcd_batch (by decide) (by decide) extra281539 15
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [281539,286539). -/
theorem batch281539 :
    Segment Valid highEstimate
      ⟨281539, 281532440907291208, 281534577313136198, 600377131139129, 600384206880252⟩
      ⟨286539, 286555084003313897, 286557302212596025, 600377131139129, 600384206880252⟩ := by
  exact part281539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
