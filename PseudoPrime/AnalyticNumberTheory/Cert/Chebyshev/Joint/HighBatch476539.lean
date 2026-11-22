/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 476539 to 481539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e476539 : Edge :=
  ⟨476539, 476622914592591850, 476626382889250586, 777716877009608, 777726748583835⟩

private def e481539 : Edge :=
  ⟨481539, 481599705875598538, 481603188962441608, 784255016805820, 784264897886886⟩

private def extra476539 : ℕ → ℕ
  | 476539 => 473
  | 477013 => 557
  | 477571 => 552
  | 478124 => 509
  | 478634 => 512
  | 479147 => 481
  | 479629 => 477
  | 480107 => 455
  | 480563 => 503
  | 481067 => 471
  | _ => 0

private theorem part476539 : Segment Valid highEstimate e476539 e481539 := by
  apply gcd_batch (by decide) (by decide) extra476539 10
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [476539,481539). -/
theorem batch476539 :
    Segment Valid highEstimate
      ⟨476539, 476622914592591850, 476626382889250586, 777716877009608, 777726748583835⟩
      ⟨481539, 481599705875598538, 481603188962441608, 784255016805820, 784264897886886⟩ := by
  exact part476539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
