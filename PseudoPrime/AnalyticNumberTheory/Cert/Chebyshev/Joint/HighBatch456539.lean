/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 456539 to 461539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e456539 : Edge :=
  ⟨456539, 456442439456991137, 456445821762249399, 764672712457974, 764682422378976⟩

private def e461539 : Edge :=
  ⟨461539, 461324724473296167, 461328128623490929, 771190383594335, 771200121195691⟩

private def extra456539 : ℕ → ℕ
  | 456539 => 456
  | 456996 => 468
  | 457465 => 534
  | 458000 => 468
  | 458469 => 397
  | 458867 => 390
  | 459258 => 443
  | 459702 => 443
  | 460146 => 351
  | 460498 => 325
  | 460824 => 286
  | 461111 => 338
  | 461450 => 88
  | _ => 0

private theorem part456539 : Segment Valid highEstimate e456539 e461539 := by
  apply gcd_batch (by decide) (by decide) extra456539 13
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [456539,461539). -/
theorem batch456539 :
    Segment Valid highEstimate
      ⟨456539, 456442439456991137, 456445821762249399, 764672712457974, 764682422378976⟩
      ⟨461539, 461324724473296167, 461328128623490929, 771190383594335, 771200121195691⟩ := by
  exact part456539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
