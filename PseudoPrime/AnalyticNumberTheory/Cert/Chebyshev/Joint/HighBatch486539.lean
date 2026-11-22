/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 486539 to 491539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e486539 : Edge :=
  ⟨486539, 486351290299917030, 486354791375405153, 784255016805820, 784264897886886⟩

private def e491539 : Edge :=
  ⟨491539, 491558605298468616, 491562135455576305, 790807522475477, 790817582073658⟩

private def extra486539 : ℕ → ℕ
  | 486539 => 382
  | 486922 => 379
  | 487302 => 379
  | 487682 => 405
  | 488088 => 432
  | 488521 => 510
  | 489032 => 523
  | 489556 => 524
  | 490081 => 536
  | 490618 => 563
  | 491182 => 356
  | _ => 0

private theorem part486539 : Segment Valid highEstimate e486539 e491539 := by
  apply gcd_batch (by decide) (by decide) extra486539 11
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [486539,491539). -/
theorem batch486539 :
    Segment Valid highEstimate
      ⟨486539, 486351290299917030, 486354791375405153, 784255016805820, 784264897886886⟩
      ⟨491539, 491558605298468616, 491562135455576305, 790807522475477, 790817582073658⟩ := by
  exact part486539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
