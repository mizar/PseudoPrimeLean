/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 941539 to 946539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e941539 : Edge :=
  ⟨941539, 941762472428818080, 941768969632513838, 1067965440766627, 1067978159843455⟩

private def e946539 : Edge :=
  ⟨946539, 946694669996915947, 946701188663639853, 1074843766737711, 1074856551461252⟩

private def extra941539 : ℕ → ℕ
  | 941539 => 503
  | 942043 => 539
  | 942583 => 507
  | 943091 => 497
  | 943589 => 533
  | 944123 => 485
  | 944609 => 569
  | 945179 => 619
  | 945799 => 611
  | 946411 => 127
  | _ => 0

private theorem part941539 : Segment Valid highEstimate e941539 e946539 := by
  apply gcd_batch (by decide) (by decide) extra941539 10
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [941539,946539). -/
theorem batch941539 :
    Segment Valid highEstimate
      ⟨941539, 941762472428818080, 941768969632513838, 1067965440766627, 1067978159843455⟩
      ⟨946539, 946694669996915947, 946701188663639853, 1074843766737711, 1074856551461252⟩ := by
  exact part941539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
