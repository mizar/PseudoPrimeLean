/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 951539 to 956539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e951539 : Edge :=
  ⟨951539, 951635682335347026, 951642233310302761, 1074843766737711, 1074856551461252⟩

private def e956539 : Edge :=
  ⟨956539, 956516597372522837, 956523151516747531, 1081728253389386, 1081741038637830⟩

private def extra951539 : ℕ → ℕ
  | 951539 => 689
  | 952229 => 697
  | 952927 => 723
  | 953651 => 727
  | 954379 => 759
  | 955139 => 751
  | 955891 => 647
  | _ => 0

private theorem part951539 : Segment Valid highEstimate e951539 e956539 := by
  apply gcd_batch (by decide) (by decide) extra951539 7
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [951539,956539). -/
theorem batch951539 :
    Segment Valid highEstimate
      ⟨951539, 951635682335347026, 951642233310302761, 1074843766737711, 1074856551461252⟩
      ⟨956539, 956516597372522837, 956523151516747531, 1081728253389386, 1081741038637830⟩ := by
  exact part951539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
