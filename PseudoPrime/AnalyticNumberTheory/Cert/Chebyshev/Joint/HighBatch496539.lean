/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 496539 to 501539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e496539 : Edge :=
  ⟨496539, 496649842794941820, 496653379998464633, 795176969632206, 795187111413169⟩

private def e501539 : Edge :=
  ⟨501539, 501714368223756912, 501717928766031837, 795176969632206, 795187111413169⟩

private def extra496539 : ℕ → ℕ
  | 496539 => 511
  | 497051 => 499
  | 497551 => 461
  | 498013 => 513
  | 498527 => 505
  | 499033 => 485
  | 499519 => 449
  | 499969 => 419
  | 500389 => 441
  | 500831 => 365
  | 501197 => 341
  | _ => 0

private theorem part496539 : Segment Valid highEstimate e496539 e501539 := by
  apply gcd_batch (by decide) (by decide) extra496539 11
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [496539,501539). -/
theorem batch496539 :
    Segment Valid highEstimate
      ⟨496539, 496649842794941820, 496653379998464633, 795176969632206, 795187111413169⟩
      ⟨501539, 501714368223756912, 501717928766031837, 795176969632206, 795187111413169⟩ := by
  exact part496539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
