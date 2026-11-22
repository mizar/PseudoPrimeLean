/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 401539 to 406539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e401539 : Edge :=
  ⟨401539, 401501442285022596, 401504570700224349, 719293395548567, 719302786537951⟩

private def e406539 : Edge :=
  ⟨406539, 406316596094030235, 406319734927542269, 719293395548567, 719302786537951⟩

private def extra401539 : ℕ → ℕ
  | 401539 => 481
  | 402021 => 412
  | 402434 => 451
  | 402886 => 464
  | 403351 => 425
  | 403777 => 374
  | 404152 => 373
  | 404526 => 426
  | 404953 => 270
  | 405224 => 270
  | 405495 => 284
  | 405780 => 335
  | 406116 => 322
  | 406439 => 99
  | _ => 0

private theorem part401539 : Segment Valid highEstimate e401539 e406539 := by
  apply gcd_batch (by decide) (by decide) extra401539 14
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [401539,406539). -/
theorem batch401539 :
    Segment Valid highEstimate
      ⟨401539, 401501442285022596, 401504570700224349, 719293395548567, 719302786537951⟩
      ⟨406539, 406316596094030235, 406319734927542269, 719293395548567, 719302786537951⟩ := by
  exact part401539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
