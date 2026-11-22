/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 316539 to 321539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e316539 : Edge :=
  ⟨316539, 316365808709960758, 316368301162602864, 623502246523567, 623510040891681⟩

private def e321539 : Edge :=
  ⟨321539, 321593397510605728, 321595949965862868, 629835526100654, 629843334818269⟩

private def extra316539 : ℕ → ℕ
  | 316539 => 276
  | 316816 => 290
  | 317107 => 335
  | 317443 => 329
  | 317773 => 366
  | 318140 => 342
  | 318483 => 417
  | 318901 => 430
  | 319332 => 400
  | 319733 => 367
  | 320101 => 347
  | 320449 => 389
  | 320839 => 399
  | 321239 => 299
  | _ => 0

private theorem part316539 : Segment Valid highEstimate e316539 e321539 := by
  apply gcd_batch (by decide) (by decide) extra316539 14
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [316539,321539). -/
theorem batch316539 :
    Segment Valid highEstimate
      ⟨316539, 316365808709960758, 316368301162602864, 623502246523567, 623510040891681⟩
      ⟨321539, 321593397510605728, 321595949965862868, 629835526100654, 629843334818269⟩ := by
  exact part316539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
