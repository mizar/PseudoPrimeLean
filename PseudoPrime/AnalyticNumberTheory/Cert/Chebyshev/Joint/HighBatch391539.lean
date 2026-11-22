/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 391539 to 396539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e391539 : Edge :=
  ⟨391539, 391479310497839496, 391482367471610861, 712846090152676, 712855418220863⟩

private def e396539 : Edge :=
  ⟨396539, 396607145088467691, 396610231591345932, 712846090152676, 712855418220863⟩

private def extra391539 : ℕ → ℕ
  | 391539 => 440
  | 391980 => 437
  | 392418 => 460
  | 392879 => 391
  | 393271 => 357
  | 393629 => 331
  | 393961 => 365
  | 394327 => 393
  | 394721 => 371
  | 395093 => 349
  | 395443 => 407
  | 395851 => 441
  | 396293 => 245
  | _ => 0

private theorem part391539 : Segment Valid highEstimate e391539 e396539 := by
  apply gcd_batch (by decide) (by decide) extra391539 13
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [391539,396539). -/
theorem batch391539 :
    Segment Valid highEstimate
      ⟨391539, 391479310497839496, 391482367471610861, 712846090152676, 712855418220863⟩
      ⟨396539, 396607145088467691, 396610231591345932, 712846090152676, 712855418220863⟩ := by
  exact part391539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
