/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 71539 to 76539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e71539 : Edge :=
  ⟨71539, 71527462009707256, 71528092128377610, 306973203214881, 306976483863075⟩

private def e76539 : Edge :=
  ⟨76539, 76516825709496550, 76517511241989268, 318170025089659, 318173836614825⟩

private def extra71539 : ℕ → ℕ
  | 71539 => 200
  | 71740 => 178
  | 71919 => 189
  | 72109 => 197
  | 72307 => 225
  | 72533 => 199
  | 72733 => 203
  | 72937 => 189
  | 73127 => 240
  | 73368 => 179
  | 73548 => 167
  | 73716 => 202
  | 73919 => 179
  | 74099 => 168
  | 74268 => 179
  | 74448 => 190
  | 74639 => 202
  | 74842 => 201
  | 75044 => 225
  | 75270 => 202
  | 75473 => 190
  | 75664 => 204
  | 75869 => 221
  | 76091 => 215
  | 76307 => 213
  | 76521 => 17
  | _ => 0

private theorem part71539 : Segment Valid highEstimate e71539 e76539 := by
  apply gcd_batch (by decide) (by decide) extra71539 26
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [71539,76539). -/
theorem batch71539 :
    Segment Valid highEstimate
      ⟨71539, 71527462009707256, 71528092128377610, 306973203214881, 306976483863075⟩
      ⟨76539, 76516825709496550, 76517511241989268, 318170025089659, 318173836614825⟩ := by
  exact part71539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
