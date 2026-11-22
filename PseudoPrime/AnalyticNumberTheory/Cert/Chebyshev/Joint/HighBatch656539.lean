/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 656539 to 661539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e656539 : Edge :=
  ⟨656539, 656330909011565733, 656335872066887132, 894156994899402, 894168258571258⟩

private def e661539 : Edge :=
  ⟨661539, 661402273677101359, 661407243801120149, 900855262095811, 900866620298927⟩

private def extra656539 : ℕ → ℕ
  | 656539 => 439
  | 656979 => 428
  | 657408 => 414
  | 657823 => 408
  | 658232 => 388
  | 658621 => 428
  | 659050 => 428
  | 659479 => 374
  | 659854 => 414
  | 660269 => 455
  | 660725 => 482
  | 661208 => 330
  | _ => 0

private theorem part656539 : Segment Valid highEstimate e656539 e661539 := by
  apply gcd_batch (by decide) (by decide) extra656539 12
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [656539,661539). -/
theorem batch656539 :
    Segment Valid highEstimate
      ⟨656539, 656330909011565733, 656335872066887132, 894156994899402, 894168258571258⟩
      ⟨661539, 661402273677101359, 661407243801120149, 900855262095811, 900866620298927⟩ := by
  exact part656539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
