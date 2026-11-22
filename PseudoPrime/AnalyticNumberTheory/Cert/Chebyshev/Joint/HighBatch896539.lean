/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 896539 to 901539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e896539 : Edge :=
  ⟨896539, 896805970329026330, 896812292898368999, 1039369630891237, 1039382218633003⟩

private def e901539 : Edge :=
  ⟨901539, 901720685380952995, 901727049257808867, 1046222929973740, 1046235522765251⟩

private def extra896539 : ℕ → ℕ
  | 896539 => 527
  | 897067 => 503
  | 897571 => 525
  | 898097 => 445
  | 898543 => 513
  | 899057 => 629
  | 899687 => 619
  | 900307 => 629
  | 900937 => 575
  | 901513 => 25
  | _ => 0

private theorem part896539 : Segment Valid highEstimate e896539 e901539 := by
  apply gcd_batch (by decide) (by decide) extra896539 10
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [896539,901539). -/
theorem batch896539 :
    Segment Valid highEstimate
      ⟨896539, 896805970329026330, 896812292898368999, 1039369630891237, 1039382218633003⟩
      ⟨901539, 901720685380952995, 901727049257808867, 1046222929973740, 1046235522765251⟩ := by
  exact part896539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
