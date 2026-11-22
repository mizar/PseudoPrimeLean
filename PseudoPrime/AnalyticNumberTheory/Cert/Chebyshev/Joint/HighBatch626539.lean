/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 626539 to 631539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e626539 : Edge :=
  ⟨626539, 626619218107783773, 626623909829185081, 880780343275270, 880791406190584⟩

private def e631539 : Edge :=
  ⟨631539, 631465971299765011, 631470683476301791, 880780343275270, 880791406190584⟩

private def extra626539 : ℕ → ℕ
  | 626539 => 531
  | 627071 => 545
  | 627617 => 571
  | 628189 => 609
  | 628799 => 656
  | 629456 => 574
  | 630031 => 653
  | 630685 => 547
  | 631233 => 305
  | _ => 0

private theorem part626539 : Segment Valid highEstimate e626539 e631539 := by
  apply gcd_batch (by decide) (by decide) extra626539 9
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [626539,631539). -/
theorem batch626539 :
    Segment Valid highEstimate
      ⟨626539, 626619218107783773, 626623909829185081, 880780343275270, 880791406190584⟩
      ⟨631539, 631465971299765011, 631470683476301791, 880780343275270, 880791406190584⟩ := by
  exact part626539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
