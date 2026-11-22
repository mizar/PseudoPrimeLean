/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 111539 to 116539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e111539 : Edge :=
  ⟨111539, 111484944561403024, 111485890653785676, 381585869620603, 381590553754195⟩

private def e116539 : Edge :=
  ⟨116539, 116486170396305392, 116487141911824128, 387405952542179, 387410641104636⟩

private def extra111539 : ℕ → ℕ
  | 111539 => 223
  | 111763 => 186
  | 111950 => 220
  | 112171 => 220
  | 112392 => 267
  | 112660 => 220
  | 112881 => 162
  | 113044 => 209
  | 113254 => 290
  | 113545 => 244
  | 113790 => 212
  | 114003 => 209
  | 114213 => 209
  | 114423 => 186
  | 114610 => 151
  | 114762 => 186
  | 114949 => 174
  | 115124 => 163
  | 115288 => 151
  | 115440 => 162
  | 115603 => 163
  | 115767 => 150
  | 115918 => 256
  | 116175 => 221
  | 116397 => 141
  | _ => 0

private theorem part111539 : Segment Valid highEstimate e111539 e116539 := by
  apply gcd_batch (by decide) (by decide) extra111539 25
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [111539,116539). -/
theorem batch111539 :
    Segment Valid highEstimate
      ⟨111539, 111484944561403024, 111485890653785676, 381585869620603, 381590553754195⟩
      ⟨116539, 116486170396305392, 116487141911824128, 387405952542179, 387410641104636⟩ := by
  exact part111539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
