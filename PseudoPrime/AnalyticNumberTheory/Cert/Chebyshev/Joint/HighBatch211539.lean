/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 211539 to 216539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e211539 : Edge :=
  ⟨211539, 211690773014747110, 211692481446359927, 524282787143811, 524288876466628⟩

private def e216539 : Edge :=
  ⟨216539, 216465261081056162, 216466996017106148, 536553910612930, 536560177875132⟩

private def extra211539 : ℕ → ℕ
  | 211539 => 187
  | 211727 => 163
  | 211891 => 225
  | 212117 => 265
  | 212383 => 285
  | 212669 => 329
  | 212999 => 289
  | 213289 => 309
  | 213599 => 347
  | 213947 => 289
  | 214237 => 281
  | 214519 => 263
  | 214783 => 339
  | 215123 => 323
  | 215447 => 379
  | 215827 => 363
  | 216191 => 347
  | _ => 0

private theorem part211539 : Segment Valid highEstimate e211539 e216539 := by
  apply gcd_batch (by decide) (by decide) extra211539 17
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [211539,216539). -/
theorem batch211539 :
    Segment Valid highEstimate
      ⟨211539, 211690773014747110, 211692481446359927, 524282787143811, 524288876466628⟩
      ⟨216539, 216465261081056162, 216466996017106148, 536553910612930, 536560177875132⟩ := by
  exact part211539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
