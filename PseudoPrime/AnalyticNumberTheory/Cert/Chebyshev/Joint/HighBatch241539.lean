/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 241539 to 246539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e241539 : Edge :=
  ⟨241539, 241459179626994363, 241461027353903130, 565367520318279, 565374043686911⟩

private def e246539 : Edge :=
  ⟨246539, 246507999558840910, 246509865452694879, 565367520318279, 565374043686911⟩

private def extra241539 : ℕ → ℕ
  | 241539 => 307
  | 241847 => 347
  | 242195 => 372
  | 242568 => 371
  | 242940 => 372
  | 243313 => 335
  | 243649 => 359
  | 244009 => 322
  | 244332 => 310
  | 244643 => 389
  | 245033 => 405
  | 245439 => 372
  | 245812 => 396
  | 246209 => 329
  | _ => 0

private theorem part241539 : Segment Valid highEstimate e241539 e246539 := by
  apply gcd_batch (by decide) (by decide) extra241539 14
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [241539,246539). -/
theorem batch241539 :
    Segment Valid highEstimate
      ⟨241539, 241459179626994363, 241461027353903130, 565367520318279, 565374043686911⟩
      ⟨246539, 246507999558840910, 246509865452694879, 565367520318279, 565374043686911⟩ := by
  exact part241539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
