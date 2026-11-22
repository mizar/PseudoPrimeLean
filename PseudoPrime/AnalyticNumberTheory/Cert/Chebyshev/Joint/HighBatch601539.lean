/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 601539 to 606539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e601539 : Edge :=
  ⟨601539, 601650083532281086, 601654522595905655, 874112115045486, 874123170639620⟩

private def e606539 : Edge :=
  ⟨606539, 606655141633597232, 606659682153251639, 874112115045486, 874123170639620⟩

private def extra601539 : ℕ → ℕ
  | 601539 => 517
  | 602057 => 443
  | 602501 => 445
  | 602947 => 509
  | 603457 => 449
  | 603907 => 453
  | 604361 => 457
  | 604819 => 429
  | 605249 => 391
  | 605641 => 435
  | 606077 => 461
  | _ => 0

private theorem part601539 : Segment Valid highEstimate e601539 e606539 := by
  apply gcd_batch (by decide) (by decide) extra601539 11
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [601539,606539). -/
theorem batch601539 :
    Segment Valid highEstimate
      ⟨601539, 601650083532281086, 601654522595905655, 874112115045486, 874123170639620⟩
      ⟨606539, 606655141633597232, 606659682153251639, 874112115045486, 874123170639620⟩ := by
  exact part601539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
