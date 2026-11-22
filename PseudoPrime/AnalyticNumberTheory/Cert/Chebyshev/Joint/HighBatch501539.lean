/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 501539 to 506539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e501539 : Edge :=
  ⟨501539, 501714368223756912, 501717928766031837, 795176969632206, 795187111413169⟩

private def e506539 : Edge :=
  ⟨506539, 506605502941265984, 506609079491755194, 801740825039943, 801750992042056⟩

private def extra501539 : ℕ → ℕ
  | 501539 => 431
  | 501971 => 527
  | 502499 => 577
  | 503077 => 562
  | 503640 => 551
  | 504192 => 577
  | 504770 => 512
  | 505283 => 427
  | 505711 => 539
  | 506251 => 287
  | _ => 0

private theorem part501539 : Segment Valid highEstimate e501539 e506539 := by
  apply gcd_batch (by decide) (by decide) extra501539 10
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [501539,506539). -/
theorem batch501539 :
    Segment Valid highEstimate
      ⟨501539, 501714368223756912, 501717928766031837, 795176969632206, 795187111413169⟩
      ⟨506539, 506605502941265984, 506609079491755194, 801740825039943, 801750992042056⟩ := by
  exact part501539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
