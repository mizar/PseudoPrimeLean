/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 161539 to 166539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e161539 : Edge :=
  ⟨161539, 161579996956010881, 161581356023361584, 464465800923861, 464471490629316⟩

private def e166539 : Edge :=
  ⟨166539, 166382984002285436, 166384385504926919, 464465800923861, 464471490629316⟩

private def extra161539 : ℕ → ℕ
  | 161539 => 243
  | 161783 => 233
  | 162017 => 341
  | 162359 => 305
  | 162665 => 281
  | 162947 => 275
  | 163223 => 293
  | 163517 => 323
  | 163841 => 305
  | 164147 => 271
  | 164419 => 281
  | 164701 => 347
  | 165049 => 299
  | 165349 => 264
  | 165614 => 300
  | 165915 => 276
  | 166192 => 227
  | 166420 => 118
  | _ => 0

private theorem part161539 : Segment Valid highEstimate e161539 e166539 := by
  apply gcd_batch (by decide) (by decide) extra161539 18
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [161539,166539). -/
theorem batch161539 :
    Segment Valid highEstimate
      ⟨161539, 161579996956010881, 161581356023361584, 464465800923861, 464471490629316⟩
      ⟨166539, 166382984002285436, 166384385504926919, 464465800923861, 464471490629316⟩ := by
  exact part161539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
