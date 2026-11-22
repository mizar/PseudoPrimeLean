/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 991539 to 996539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e991539 : Edge :=
  ⟨991539, 991140935656725200, 991147608655976359, 1095517575725254, 1095530504794266⟩

private def e996539 : Edge :=
  ⟨996539, 996077836842586904, 996084532522276670, 1102422326452684, 1102435268224133⟩

private def extra991539 : ℕ → ℕ
  | 991539 => 397
  | 991937 => 427
  | 992365 => 455
  | 992821 => 386
  | 993208 => 372
  | 993581 => 358
  | 993940 => 317
  | 994258 => 351
  | 994610 => 372
  | 994983 => 400
  | 995384 => 372
  | 995757 => 400
  | 996158 => 344
  | 996503 => 35
  | _ => 0

private theorem part991539 : Segment Valid highEstimate e991539 e996539 := by
  apply gcd_batch (by decide) (by decide) extra991539 14
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [991539,996539). -/
theorem batch991539 :
    Segment Valid highEstimate
      ⟨991539, 991140935656725200, 991147608655976359, 1095517575725254, 1095530504794266⟩
      ⟨996539, 996077836842586904, 996084532522276670, 1102422326452684, 1102435268224133⟩ := by
  exact part991539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
