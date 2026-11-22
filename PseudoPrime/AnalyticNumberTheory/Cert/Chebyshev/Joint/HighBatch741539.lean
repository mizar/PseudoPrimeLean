/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 741539 to 746539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e741539 : Edge :=
  ⟨741539, 741593991365195835, 741599531318049378, 962562871258316, 962574760588496⟩

private def e746539 : Edge :=
  ⟨746539, 746305661307613763, 746311216772775337, 969323284128657, 969335329903535⟩

private def extra741539 : ℕ → ℕ
  | 741539 => 661
  | 742201 => 689
  | 742891 => 689
  | 743581 => 662
  | 744244 => 567
  | 744812 => 520
  | 745333 => 459
  | 745793 => 431
  | 746225 => 313
  | _ => 0

private theorem part741539 : Segment Valid highEstimate e741539 e746539 := by
  apply gcd_batch (by decide) (by decide) extra741539 9
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [741539,746539). -/
theorem batch741539 :
    Segment Valid highEstimate
      ⟨741539, 741593991365195835, 741599531318049378, 962562871258316, 962574760588496⟩
      ⟨746539, 746305661307613763, 746311216772775337, 969323284128657, 969335329903535⟩ := by
  exact part741539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
