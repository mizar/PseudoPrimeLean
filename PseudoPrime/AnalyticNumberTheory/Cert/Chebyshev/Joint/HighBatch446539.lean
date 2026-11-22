/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 446539 to 451539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e446539 : Edge :=
  ⟨446539, 446709666635591964, 446713004250775895, 758160967129436, 758170675943213⟩

private def e451539 : Edge :=
  ⟨451539, 451642371235837931, 451645740542203779, 758160967129436, 758170675943213⟩

private def extra446539 : ℕ → ℕ
  | 446539 => 429
  | 446969 => 469
  | 447439 => 461
  | 447901 => 477
  | 448379 => 596
  | 448976 => 468
  | 449445 => 543
  | 449989 => 441
  | 450431 => 397
  | 450829 => 371
  | 451201 => 337
  | _ => 0

private theorem part446539 : Segment Valid highEstimate e446539 e451539 := by
  apply gcd_batch (by decide) (by decide) extra446539 11
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [446539,451539). -/
theorem batch446539 :
    Segment Valid highEstimate
      ⟨446539, 446709666635591964, 446713004250775895, 758160967129436, 758170675943213⟩
      ⟨451539, 451642371235837931, 451645740542203779, 758160967129436, 758170675943213⟩ := by
  exact part446539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
