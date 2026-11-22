/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 926539 to 931539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e926539 : Edge :=
  ⟨926539, 926922224503257658, 926928663976648094, 1061091242399709, 1061103934892325⟩

private def e931539 : Edge :=
  ⟨931539, 931718142652967269, 931724610039269399, 1061091242399709, 1061103934892325⟩

private def extra926539 : ℕ → ℕ
  | 926539 => 363
  | 926903 => 413
  | 927317 => 461
  | 927779 => 493
  | 928273 => 519
  | 928793 => 467
  | 929261 => 431
  | 929693 => 463
  | 930157 => 461
  | 930619 => 533
  | 931153 => 385
  | _ => 0

private theorem part926539 : Segment Valid highEstimate e926539 e931539 := by
  apply gcd_batch (by decide) (by decide) extra926539 11
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [926539,931539). -/
theorem batch926539 :
    Segment Valid highEstimate
      ⟨926539, 926922224503257658, 926928663976648094, 1061091242399709, 1061103934892325⟩
      ⟨931539, 931718142652967269, 931724610039269399, 1061091242399709, 1061103934892325⟩ := by
  exact part926539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
