/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 166539 to 171539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e166539 : Edge :=
  ⟨166539, 166382984002285436, 166384385504926919, 464465800923861, 464471490629316⟩

private def e171539 : Edge :=
  ⟨171539, 171372592019184065, 171374042348927662, 470479516074996, 470485208784114⟩

private def extra166539 : ℕ → ℕ
  | 166539 => 169
  | 166709 => 228
  | 166938 => 227
  | 167166 => 288
  | 167455 => 315
  | 167771 => 264
  | 168036 => 228
  | 168265 => 204
  | 168470 => 180
  | 168651 => 168
  | 168820 => 144
  | 168965 => 120
  | 169086 => 131
  | 169218 => 120
  | 169339 => 144
  | 169484 => 120
  | 169605 => 107
  | 169713 => 144
  | 169858 => 144
  | 170003 => 168
  | 170172 => 144
  | 170317 => 180
  | 170498 => 204
  | 170703 => 191
  | 170895 => 241
  | 171137 => 216
  | 171354 => 184
  | _ => 0

private theorem part166539 : Segment Valid highEstimate e166539 e171539 := by
  apply gcd_batch (by decide) (by decide) extra166539 27
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [166539,171539). -/
theorem batch166539 :
    Segment Valid highEstimate
      ⟨166539, 166382984002285436, 166384385504926919, 464465800923861, 464471490629316⟩
      ⟨171539, 171372592019184065, 171374042348927662, 470479516074996, 470485208784114⟩ := by
  exact part166539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
