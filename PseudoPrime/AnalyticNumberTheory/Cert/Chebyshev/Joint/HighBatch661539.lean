/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 661539 to 666539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e661539 : Edge :=
  ⟨661539, 661402273677101359, 661407243801120149, 900855262095811, 900866620298927⟩

private def e666539 : Edge :=
  ⟨666539, 666416161902772199, 666421165805543381, 900855262095811, 900866620298927⟩

private def extra661539 : ℕ → ℕ
  | 661539 => 513
  | 662053 => 468
  | 662522 => 442
  | 662965 => 481
  | 663447 => 429
  | 663877 => 441
  | 664319 => 495
  | 664815 => 576
  | 665392 => 616
  | 666009 => 529
  | _ => 0

private theorem part661539 : Segment Valid highEstimate e661539 e666539 := by
  apply gcd_batch (by decide) (by decide) extra661539 10
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [661539,666539). -/
theorem batch661539 :
    Segment Valid highEstimate
      ⟨661539, 661402273677101359, 661407243801120149, 900855262095811, 900866620298927⟩
      ⟨666539, 666416161902772199, 666421165805543381, 900855262095811, 900866620298927⟩ := by
  exact part661539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
