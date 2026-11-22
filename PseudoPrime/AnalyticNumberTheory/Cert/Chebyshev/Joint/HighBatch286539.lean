/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 286539 to 291539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e286539 : Edge :=
  ⟨286539, 286555084003313897, 286557302212596025, 600377131139129, 600384206880252⟩

private def e291539 : Edge :=
  ⟨291539, 291509441890940974, 291511685352571087, 600377131139129, 600384206880252⟩

private def extra286539 : ℕ → ℕ
  | 286539 => 443
  | 286983 => 399
  | 287383 => 454
  | 287838 => 326
  | 288165 => 251
  | 288417 => 276
  | 288694 => 276
  | 288971 => 238
  | 289210 => 351
  | 289562 => 351
  | 289914 => 339
  | 290254 => 389
  | 290644 => 390
  | 291035 => 389
  | 291425 => 113
  | _ => 0

private theorem part286539 : Segment Valid highEstimate e286539 e291539 := by
  apply gcd_batch (by decide) (by decide) extra286539 15
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [286539,291539). -/
theorem batch286539 :
    Segment Valid highEstimate
      ⟨286539, 286555084003313897, 286557302212596025, 600377131139129, 600384206880252⟩
      ⟨291539, 291509441890940974, 291511685352571087, 600377131139129, 600384206880252⟩ := by
  exact part286539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
