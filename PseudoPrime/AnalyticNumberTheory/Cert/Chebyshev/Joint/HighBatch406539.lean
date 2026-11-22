/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 406539 to 411539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e406539 : Edge :=
  ⟨406539, 406316596094030235, 406319734927542269, 719293395548567, 719302786537951⟩

private def e411539 : Edge :=
  ⟨411539, 411349557745615430, 411352730760635390, 725756425004208, 725765817214306⟩

private def extra406539 : ℕ → ℕ
  | 406539 => 286
  | 406826 => 284
  | 407111 => 167
  | 407279 => 206
  | 407486 => 205
  | 407692 => 219
  | 407912 => 258
  | 408171 => 244
  | 408416 => 284
  | 408701 => 296
  | 408998 => 296
  | 409295 => 284
  | 409580 => 296
  | 409877 => 297
  | 410175 => 335
  | 410511 => 361
  | 410873 => 348
  | 411222 => 316
  | _ => 0

private theorem part406539 : Segment Valid highEstimate e406539 e411539 := by
  apply gcd_batch (by decide) (by decide) extra406539 18
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [406539,411539). -/
theorem batch406539 :
    Segment Valid highEstimate
      ⟨406539, 406316596094030235, 406319734927542269, 719293395548567, 719302786537951⟩
      ⟨411539, 411349557745615430, 411352730760635390, 725756425004208, 725765817214306⟩ := by
  exact part406539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
