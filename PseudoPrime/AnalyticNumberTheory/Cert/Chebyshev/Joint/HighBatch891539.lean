/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 891539 to 896539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e891539 : Edge :=
  ⟨891539, 891694581140459969, 891700882763878255, 1039369630891237, 1039382218633003⟩

private def e896539 : Edge :=
  ⟨896539, 896805970329026330, 896812292898368999, 1039369630891237, 1039382218633003⟩

private def extra891539 : ℕ → ℕ
  | 891539 => 487
  | 892027 => 503
  | 892531 => 509
  | 893041 => 467
  | 893509 => 563
  | 894073 => 467
  | 894541 => 509
  | 895051 => 501
  | 895553 => 433
  | 895987 => 503
  | 896491 => 47
  | _ => 0

private theorem part891539 : Segment Valid highEstimate e891539 e896539 := by
  apply gcd_batch (by decide) (by decide) extra891539 11
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [891539,896539). -/
theorem batch891539 :
    Segment Valid highEstimate
      ⟨891539, 891694581140459969, 891700882763878255, 1039369630891237, 1039382218633003⟩
      ⟨896539, 896805970329026330, 896812292898368999, 1039369630891237, 1039382218633003⟩ := by
  exact part891539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
