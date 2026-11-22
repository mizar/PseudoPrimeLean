/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 776539 to 781539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e776539 : Edge :=
  ⟨776539, 776411802478420273, 776417541711842328, 982880847623670, 982893007239747⟩

private def e781539 : Edge :=
  ⟨781539, 781532914755499894, 781538680576363060, 989664172811091, 989676338238130⟩

private def extra776539 : ℕ → ℕ
  | 776539 => 577
  | 777117 => 541
  | 777659 => 583
  | 778243 => 609
  | 778853 => 651
  | 779505 => 569
  | 780075 => 644
  | 780720 => 569
  | 781290 => 248
  | _ => 0

private theorem part776539 : Segment Valid highEstimate e776539 e781539 := by
  apply gcd_batch (by decide) (by decide) extra776539 9
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [776539,781539). -/
theorem batch776539 :
    Segment Valid highEstimate
      ⟨776539, 776411802478420273, 776417541711842328, 982880847623670, 982893007239747⟩
      ⟨781539, 781532914755499894, 781538680576363060, 989664172811091, 989676338238130⟩ := by
  exact part776539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
