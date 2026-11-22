/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 171539 to 176539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e171539 : Edge :=
  ⟨171539, 171372592019184065, 171374042348927662, 470479516074996, 470485208784114⟩

private def e176539 : Edge :=
  ⟨176539, 176458855475595456, 176460348802168409, 476517386870567, 476523105582838⟩

private def extra171539 : ℕ → ℕ
  | 171539 => 176
  | 171716 => 204
  | 171921 => 216
  | 172138 => 180
  | 172319 => 216
  | 172536 => 216
  | 172753 => 277
  | 173031 => 253
  | 173285 => 240
  | 173526 => 168
  | 173695 => 192
  | 173888 => 205
  | 174094 => 252
  | 174347 => 253
  | 174601 => 216
  | 174818 => 217
  | 175036 => 204
  | 175241 => 132
  | 175374 => 120
  | 175495 => 120
  | 175616 => 78
  | 175695 => 95
  | 175791 => 108
  | 175900 => 108
  | 176009 => 120
  | 176130 => 156
  | 176287 => 156
  | 176444 => 94
  | _ => 0

private theorem part171539 : Segment Valid highEstimate e171539 e176539 := by
  apply gcd_batch (by decide) (by decide) extra171539 28
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [171539,176539). -/
theorem batch171539 :
    Segment Valid highEstimate
      ⟨171539, 171372592019184065, 171374042348927662, 470479516074996, 470485208784114⟩
      ⟨176539, 176458855475595456, 176460348802168409, 476517386870567, 476523105582838⟩ := by
  exact part171539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
