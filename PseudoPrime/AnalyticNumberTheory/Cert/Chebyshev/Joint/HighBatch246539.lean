/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 246539 to 251539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e246539 : Edge :=
  ⟨246539, 246507999558840910, 246509865452694879, 565367520318279, 565374043686911⟩

private def e251539 : Edge :=
  ⟨251539, 251645861104826777, 251647743667137801, 571580126340599, 571586668000734⟩

private def extra246539 : ℕ → ℕ
  | 246539 => 377
  | 246917 => 410
  | 247328 => 359
  | 247688 => 368
  | 248057 => 331
  | 248389 => 317
  | 248707 => 279
  | 248987 => 299
  | 249287 => 253
  | 249541 => 291
  | 249833 => 239
  | 250073 => 359
  | 250433 => 403
  | 250837 => 363
  | 251201 => 311
  | 251513 => 25
  | _ => 0

private theorem part246539 : Segment Valid highEstimate e246539 e251539 := by
  apply gcd_batch (by decide) (by decide) extra246539 16
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [246539,251539). -/
theorem batch246539 :
    Segment Valid highEstimate
      ⟨246539, 246507999558840910, 246509865452694879, 565367520318279, 565374043686911⟩
      ⟨251539, 251645861104826777, 251647743667137801, 571580126340599, 571586668000734⟩ := by
  exact part246539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
