/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 736539 to 741539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e736539 : Edge :=
  ⟨736539, 736654950214771859, 736660476226230268, 955807103056896, 955818908254589⟩

private def e741539 : Edge :=
  ⟨741539, 741593991365195835, 741599531318049378, 962562871258316, 962574760588496⟩

private def extra736539 : ℕ → ℕ
  | 736539 => 619
  | 737159 => 593
  | 737753 => 625
  | 738379 => 641
  | 739021 => 527
  | 739549 => 549
  | 740099 => 571
  | 740671 => 611
  | 741283 => 255
  | _ => 0

private theorem part736539 : Segment Valid highEstimate e736539 e741539 := by
  apply gcd_batch (by decide) (by decide) extra736539 9
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [736539,741539). -/
theorem batch736539 :
    Segment Valid highEstimate
      ⟨736539, 736654950214771859, 736660476226230268, 955807103056896, 955818908254589⟩
      ⟨741539, 741593991365195835, 741599531318049378, 962562871258316, 962574760588496⟩ := by
  exact part736539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
