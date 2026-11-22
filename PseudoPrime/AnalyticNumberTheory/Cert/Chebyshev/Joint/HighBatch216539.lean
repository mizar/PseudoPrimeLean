/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 216539 to 221539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e216539 : Edge :=
  ⟨216539, 216465261081056162, 216466996017106148, 536553910612930, 536560177875132⟩

private def e221539 : Edge :=
  ⟨221539, 221562348463509236, 221564110857657096, 542700239780932, 542706527944601⟩

private def extra216539 : ℕ → ℕ
  | 216539 => 292
  | 216832 => 319
  | 217152 => 282
  | 217435 => 368
  | 217804 => 344
  | 218149 => 332
  | 218482 => 282
  | 218765 => 319
  | 219085 => 357
  | 219443 => 319
  | 219763 => 293
  | 220057 => 341
  | 220399 => 357
  | 220757 => 325
  | 221083 => 363
  | 221447 => 91
  | _ => 0

private theorem part216539 : Segment Valid highEstimate e216539 e221539 := by
  apply gcd_batch (by decide) (by decide) extra216539 16
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [216539,221539). -/
theorem batch216539 :
    Segment Valid highEstimate
      ⟨216539, 216465261081056162, 216466996017106148, 536553910612930, 536560177875132⟩
      ⟨221539, 221562348463509236, 221564110857657096, 542700239780932, 542706527944601⟩ := by
  exact part216539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
