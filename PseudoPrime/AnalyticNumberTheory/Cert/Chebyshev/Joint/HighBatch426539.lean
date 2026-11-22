/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 426539 to 431539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e426539 : Edge :=
  ⟨426539, 426321040858886838, 426324296122481337, 745176489933631, 745186159243371⟩

private def e431539 : Edge :=
  ⟨431539, 431443924113567568, 431447191929929561, 745176489933631, 745186159243371⟩

private def extra426539 : ℕ → ℕ
  | 426539 => 303
  | 426843 => 336
  | 427180 => 337
  | 427518 => 388
  | 427907 => 310
  | 428218 => 363
  | 428582 => 362
  | 428945 => 297
  | 429243 => 272
  | 429516 => 323
  | 429840 => 363
  | 430204 => 401
  | 430606 => 350
  | 430957 => 414
  | 431372 => 166
  | _ => 0

private theorem part426539 : Segment Valid highEstimate e426539 e431539 := by
  apply gcd_batch (by decide) (by decide) extra426539 15
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [426539,431539). -/
theorem batch426539 :
    Segment Valid highEstimate
      ⟨426539, 426321040858886838, 426324296122481337, 745176489933631, 745186159243371⟩
      ⟨431539, 431443924113567568, 431447191929929561, 745176489933631, 745186159243371⟩ := by
  exact part426539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
