/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 966539 to 971539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e966539 : Edge :=
  ⟨966539, 966566468497449366, 966573077998451939, 1088618862387204, 1088631673355392⟩

private def e971539 : Edge :=
  ⟨971539, 971597689847870591, 971604302142994180, 1088618862387204, 1088631673355392⟩

private def extra966539 : ℕ → ℕ
  | 966539 => 813
  | 967353 => 674
  | 968028 => 703
  | 968732 => 757
  | 969490 => 716
  | 970207 => 689
  | 970897 => 641
  | _ => 0

private theorem part966539 : Segment Valid highEstimate e966539 e971539 := by
  apply gcd_batch (by decide) (by decide) extra966539 7
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [966539,971539). -/
theorem batch966539 :
    Segment Valid highEstimate
      ⟨966539, 966566468497449366, 966573077998451939, 1088618862387204, 1088631673355392⟩
      ⟨971539, 971597689847870591, 971604302142994180, 1088618862387204, 1088631673355392⟩ := by
  exact part966539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
