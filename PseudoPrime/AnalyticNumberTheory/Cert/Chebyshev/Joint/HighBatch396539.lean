/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 396539 to 401539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e396539 : Edge :=
  ⟨396539, 396607145088467691, 396610231591345932, 712846090152676, 712855418220863⟩

private def e401539 : Edge :=
  ⟨401539, 401501442285022596, 401504570700224349, 719293395548567, 719302786537951⟩

private def extra396539 : ℕ → ℕ
  | 396539 => 473
  | 397013 => 479
  | 397493 => 487
  | 397981 => 425
  | 398407 => 425
  | 398833 => 407
  | 399241 => 401
  | 399643 => 389
  | 400033 => 395
  | 400429 => 473
  | 400903 => 503
  | 401407 => 131
  | _ => 0

private theorem part396539 : Segment Valid highEstimate e396539 e401539 := by
  apply gcd_batch (by decide) (by decide) extra396539 12
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [396539,401539). -/
theorem batch396539 :
    Segment Valid highEstimate
      ⟨396539, 396607145088467691, 396610231591345932, 712846090152676, 712855418220863⟩
      ⟨401539, 401501442285022596, 401504570700224349, 719293395548567, 719302786537951⟩ := by
  exact part396539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
