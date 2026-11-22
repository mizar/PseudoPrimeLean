/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 586539 to 591539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e586539 : Edge :=
  ⟨586539, 586587342277331237, 586591639149956020, 860816745119682, 860827778673321⟩

private def e591539 : Edge :=
  ⟨591539, 591589524179017132, 591593905744761192, 867461836088443, 867472870489804⟩

private def extra586539 : ℕ → ℕ
  | 586539 => 481
  | 587021 => 437
  | 587459 => 353
  | 587813 => 307
  | 588121 => 315
  | 588437 => 335
  | 588773 => 389
  | 589163 => 415
  | 589579 => 453
  | 590033 => 455
  | 590489 => 497
  | 590987 => 551
  | _ => 0

private theorem part586539 : Segment Valid highEstimate e586539 e591539 := by
  apply gcd_batch (by decide) (by decide) extra586539 12
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [586539,591539). -/
theorem batch586539 :
    Segment Valid highEstimate
      ⟨586539, 586587342277331237, 586591639149956020, 860816745119682, 860827778673321⟩
      ⟨591539, 591589524179017132, 591593905744761192, 867461836088443, 867472870489804⟩ := by
  exact part586539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
