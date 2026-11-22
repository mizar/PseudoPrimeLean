/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 421539 to 426539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e421539 : Edge :=
  ⟨421539, 421416649240886826, 421419867687234253, 738694915556115, 738704378567016⟩

private def e426539 : Edge :=
  ⟨426539, 426321040858886838, 426324296122481337, 745176489933631, 745186159243371⟩

private def extra421539 : ℕ → ℕ
  | 421539 => 396
  | 421936 => 349
  | 422286 => 362
  | 422649 => 336
  | 422986 => 336
  | 423323 => 426
  | 423750 => 401
  | 424152 => 453
  | 424606 => 453
  | 425060 => 466
  | 425527 => 479
  | 426007 => 427
  | 426435 => 103
  | _ => 0

private theorem part421539 : Segment Valid highEstimate e421539 e426539 := by
  apply gcd_batch (by decide) (by decide) extra421539 13
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [421539,426539). -/
theorem batch421539 :
    Segment Valid highEstimate
      ⟨421539, 421416649240886826, 421419867687234253, 738694915556115, 738704378567016⟩
      ⟨426539, 426321040858886838, 426324296122481337, 745176489933631, 745186159243371⟩ := by
  exact part421539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
