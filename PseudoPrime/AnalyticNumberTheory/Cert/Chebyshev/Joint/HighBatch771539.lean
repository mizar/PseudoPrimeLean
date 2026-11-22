/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 771539 to 776539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e771539 : Edge :=
  ⟨771539, 771564332433043628, 771570066296020882, 976099789998232, 976111948968637⟩

private def e776539 : Edge :=
  ⟨776539, 776411802478420273, 776417541711842328, 982880847623670, 982893007239747⟩

private def extra771539 : ℕ → ℕ
  | 771539 => 691
  | 772231 => 713
  | 772945 => 664
  | 773610 => 672
  | 774283 => 736
  | 775020 => 664
  | 775685 => 623
  | 776309 => 229
  | _ => 0

private theorem part771539 : Segment Valid highEstimate e771539 e776539 := by
  apply gcd_batch (by decide) (by decide) extra771539 8
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [771539,776539). -/
theorem batch771539 :
    Segment Valid highEstimate
      ⟨771539, 771564332433043628, 771570066296020882, 976099789998232, 976111948968637⟩
      ⟨776539, 776411802478420273, 776417541711842328, 982880847623670, 982893007239747⟩ := by
  exact part771539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
