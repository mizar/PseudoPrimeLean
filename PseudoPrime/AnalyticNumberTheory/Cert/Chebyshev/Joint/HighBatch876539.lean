/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 876539 to 881539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e876539 : Edge :=
  ⟨876539, 876756398738757828, 876762633607524403, 1025680005678137, 1025692448270876⟩

private def e881539 : Edge :=
  ⟨881539, 881909430338492309, 881915694672363901, 1032522688658498, 1032535178279526⟩

private def extra876539 : ℕ → ℕ
  | 876539 => 569
  | 877109 => 629
  | 877739 => 559
  | 878299 => 551
  | 878851 => 519
  | 879371 => 509
  | 879881 => 479
  | 880361 => 457
  | 880819 => 399
  | 881219 => 319
  | _ => 0

private theorem part876539 : Segment Valid highEstimate e876539 e881539 := by
  apply gcd_batch (by decide) (by decide) extra876539 10
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [876539,881539). -/
theorem batch876539 :
    Segment Valid highEstimate
      ⟨876539, 876756398738757828, 876762633607524403, 1025680005678137, 1025692448270876⟩
      ⟨881539, 881909430338492309, 881915694672363901, 1032522688658498, 1032535178279526⟩ := by
  exact part876539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
