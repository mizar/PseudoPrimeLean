/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 311539 to 316539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e311539 : Edge :=
  ⟨311539, 311264949902066446, 311267422545720665, 623502246523567, 623510040891681⟩

private def e316539 : Edge :=
  ⟨316539, 316365808709960758, 316368301162602864, 623502246523567, 623510040891681⟩

private def extra311539 : ℕ → ℕ
  | 311539 => 184
  | 311724 => 189
  | 311914 => 163
  | 312078 => 151
  | 312230 => 164
  | 312395 => 201
  | 312597 => 202
  | 312800 => 227
  | 313028 => 214
  | 313243 => 202
  | 313446 => 214
  | 313661 => 240
  | 313902 => 239
  | 314142 => 291
  | 314434 => 303
  | 314738 => 303
  | 315042 => 265
  | 315308 => 227
  | 315536 => 252
  | 315789 => 265
  | 316055 => 253
  | 316309 => 229
  | _ => 0

private theorem part311539 : Segment Valid highEstimate e311539 e316539 := by
  apply gcd_batch (by decide) (by decide) extra311539 22
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [311539,316539). -/
theorem batch311539 :
    Segment Valid highEstimate
      ⟨311539, 311264949902066446, 311267422545720665, 623502246523567, 623510040891681⟩
      ⟨316539, 316365808709960758, 316368301162602864, 623502246523567, 623510040891681⟩ := by
  exact part311539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
