/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 931539 to 936539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e931539 : Edge :=
  ⟨931539, 931718142652967269, 931724610039269399, 1061091242399709, 1061103934892325⟩

private def e936539 : Edge :=
  ⟨936539, 936770254416712369, 936776745537277321, 1067965440766627, 1067978159843455⟩

private def extra931539 : ℕ → ℕ
  | 931539 => 577
  | 932117 => 491
  | 932609 => 547
  | 933157 => 623
  | 933781 => 537
  | 934319 => 511
  | 934831 => 471
  | 935303 => 467
  | 935771 => 547
  | 936319 => 219
  | _ => 0

private theorem part931539 : Segment Valid highEstimate e931539 e936539 := by
  apply gcd_batch (by decide) (by decide) extra931539 10
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [931539,936539). -/
theorem batch931539 :
    Segment Valid highEstimate
      ⟨931539, 931718142652967269, 931724610039269399, 1061091242399709, 1061103934892325⟩
      ⟨936539, 936770254416712369, 936776745537277321, 1067965440766627, 1067978159843455⟩ := by
  exact part931539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
