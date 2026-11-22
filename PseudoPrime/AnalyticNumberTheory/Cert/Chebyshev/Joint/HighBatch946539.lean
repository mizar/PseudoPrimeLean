/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 946539 to 951539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e946539 : Edge :=
  ⟨946539, 946694669996915947, 946701188663639853, 1074843766737711, 1074856551461252⟩

private def e951539 : Edge :=
  ⟨951539, 951635682335347026, 951642233310302761, 1074843766737711, 1074856551461252⟩

private def extra946539 : ℕ → ℕ
  | 946539 => 663
  | 947203 => 669
  | 947873 => 673
  | 948547 => 833
  | 949381 => 721
  | 950103 => 687
  | 950791 => 645
  | 951437 => 101
  | _ => 0

private theorem part946539 : Segment Valid highEstimate e946539 e951539 := by
  apply gcd_batch (by decide) (by decide) extra946539 8
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [946539,951539). -/
theorem batch946539 :
    Segment Valid highEstimate
      ⟨946539, 946694669996915947, 946701188663639853, 1074843766737711, 1074856551461252⟩
      ⟨951539, 951635682335347026, 951642233310302761, 1074843766737711, 1074856551461252⟩ := by
  exact part946539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
