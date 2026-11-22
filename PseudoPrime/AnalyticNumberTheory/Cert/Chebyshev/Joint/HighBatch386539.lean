/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 386539 to 391539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e386539 : Edge :=
  ⟨386539, 386530700350060504, 386533732838157433, 706946193682963, 706955425300522⟩

private def e391539 : Edge :=
  ⟨391539, 391479310497839496, 391482367471610861, 712846090152676, 712855418220863⟩

private def extra386539 : ℕ → ℕ
  | 386539 => 488
  | 387028 => 437
  | 387466 => 411
  | 387878 => 346
  | 388225 => 334
  | 388560 => 321
  | 388882 => 282
  | 389165 => 326
  | 389492 => 295
  | 389788 => 334
  | 390123 => 398
  | 390522 => 463
  | 390986 => 413
  | 391400 => 138
  | _ => 0

private theorem part386539 : Segment Valid highEstimate e386539 e391539 := by
  apply gcd_batch (by decide) (by decide) extra386539 14
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [386539,391539). -/
theorem batch386539 :
    Segment Valid highEstimate
      ⟨386539, 386530700350060504, 386533732838157433, 706946193682963, 706955425300522⟩
      ⟨391539, 391479310497839496, 391482367471610861, 712846090152676, 712855418220863⟩ := by
  exact part386539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
