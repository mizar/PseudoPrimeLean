/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 691539 to 696539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e691539 : Edge :=
  ⟨691539, 691312311202672969, 691317524145104807, 927716763830316, 927728395365848⟩

private def e696539 : Edge :=
  ⟨696539, 696477191823668755, 696482419560906906, 927716763830316, 927728395365848⟩

private def extra691539 : ℕ → ℕ
  | 691539 => 437
  | 691977 => 524
  | 692502 => 591
  | 693094 => 564
  | 693659 => 524
  | 694184 => 510
  | 694695 => 605
  | 695301 => 604
  | 695906 => 632
  | _ => 0

private theorem part691539 : Segment Valid highEstimate e691539 e696539 := by
  apply gcd_batch (by decide) (by decide) extra691539 9
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [691539,696539). -/
theorem batch691539 :
    Segment Valid highEstimate
      ⟨691539, 691312311202672969, 691317524145104807, 927716763830316, 927728395365848⟩
      ⟨696539, 696477191823668755, 696482419560906906, 927716763830316, 927728395365848⟩ := by
  exact part691539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
