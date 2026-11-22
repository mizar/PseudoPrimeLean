/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 481539 to 486539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e481539 : Edge :=
  ⟨481539, 481599705875598538, 481603188962441608, 784255016805820, 784264897886886⟩

private def e486539 : Edge :=
  ⟨486539, 486351290299917030, 486354791375405153, 784255016805820, 784264897886886⟩

private def extra481539 : ℕ → ℕ
  | 481539 => 493
  | 482033 => 479
  | 482513 => 403
  | 482917 => 471
  | 483389 => 437
  | 483827 => 455
  | 484283 => 493
  | 484777 => 624
  | 485402 => 445
  | 485848 => 379
  | 486228 => 310
  | _ => 0

private theorem part481539 : Segment Valid highEstimate e481539 e486539 := by
  apply gcd_batch (by decide) (by decide) extra481539 11
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [481539,486539). -/
theorem batch481539 :
    Segment Valid highEstimate
      ⟨481539, 481599705875598538, 481603188962441608, 784255016805820, 784264897886886⟩
      ⟨486539, 486351290299917030, 486354791375405153, 784255016805820, 784264897886886⟩ := by
  exact part481539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
