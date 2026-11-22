/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 581539 to 586539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e581539 : Edge :=
  ⟨581539, 581568358105352654, 581572589078747123, 860816745119682, 860827778673321⟩

private def e586539 : Edge :=
  ⟨586539, 586587342277331237, 586591639149956020, 860816745119682, 860827778673321⟩

private def extra581539 : ℕ → ℕ
  | 581539 => 579
  | 582119 => 611
  | 582731 => 569
  | 583301 => 557
  | 583859 => 649
  | 584509 => 561
  | 585071 => 599
  | 585671 => 517
  | 586189 => 349
  | _ => 0

private theorem part581539 : Segment Valid highEstimate e581539 e586539 := by
  apply gcd_batch (by decide) (by decide) extra581539 9
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [581539,586539). -/
theorem batch581539 :
    Segment Valid highEstimate
      ⟨581539, 581568358105352654, 581572589078747123, 860816745119682, 860827778673321⟩
      ⟨586539, 586587342277331237, 586591639149956020, 860816745119682, 860827778673321⟩ := by
  exact part581539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
