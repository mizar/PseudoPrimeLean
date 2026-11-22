/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 531539 to 536539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e531539 : Edge :=
  ⟨531539, 531702746726333935, 531706404388295137, 816699368866669, 816709810119861⟩

private def e536539 : Edge :=
  ⟨536539, 536701085652854120, 536704810452442472, 816699368866669, 816709810119861⟩

private def extra531539 : ℕ → ℕ
  | 531539 => 437
  | 531977 => 401
  | 532379 => 371
  | 532751 => 359
  | 533111 => 341
  | 533453 => 433
  | 533887 => 365
  | 534253 => 393
  | 534647 => 475
  | 535123 => 513
  | 535637 => 509
  | 536147 => 391
  | _ => 0

private theorem part531539 : Segment Valid highEstimate e531539 e536539 := by
  apply gcd_batch (by decide) (by decide) extra531539 12
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [531539,536539). -/
theorem batch531539 :
    Segment Valid highEstimate
      ⟨531539, 531702746726333935, 531706404388295137, 816699368866669, 816709810119861⟩
      ⟨536539, 536701085652854120, 536704810452442472, 816699368866669, 816709810119861⟩ := by
  exact part531539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
