/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 631539 to 636539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e631539 : Edge :=
  ⟨631539, 631465971299765011, 631470683476301791, 880780343275270, 880791406190584⟩

private def e636539 : Edge :=
  ⟨636539, 636589465506940966, 636594243338504390, 887461196452993, 887472396843589⟩

private def extra631539 : ℕ → ℕ
  | 631539 => 562
  | 632102 => 596
  | 632699 => 671
  | 633371 => 587
  | 633959 => 587
  | 634547 => 641
  | 635189 => 587
  | 635777 => 535
  | 636313 => 225
  | _ => 0

private theorem part631539 : Segment Valid highEstimate e631539 e636539 := by
  apply gcd_batch (by decide) (by decide) extra631539 9
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [631539,636539). -/
theorem batch631539 :
    Segment Valid highEstimate
      ⟨631539, 631465971299765011, 631470683476301791, 880780343275270, 880791406190584⟩
      ⟨636539, 636589465506940966, 636594243338504390, 887461196452993, 887472396843589⟩ := by
  exact part631539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
