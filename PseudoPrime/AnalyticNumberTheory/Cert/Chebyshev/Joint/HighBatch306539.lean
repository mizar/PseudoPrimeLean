/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 306539 to 311539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e306539 : Edge :=
  ⟨306539, 306454995417763145, 306457397240772409, 617179685752607, 617187194586000⟩

private def e311539 : Edge :=
  ⟨311539, 311264949902066446, 311267422545720665, 623502246523567, 623510040891681⟩

private def extra306539 : ℕ → ℕ
  | 306539 => 358
  | 306898 => 353
  | 307252 => 340
  | 307593 => 366
  | 307960 => 302
  | 308263 => 252
  | 308516 => 265
  | 308782 => 239
  | 309022 => 265
  | 309288 => 277
  | 309566 => 303
  | 309870 => 290
  | 310161 => 239
  | 310401 => 233
  | 310635 => 240
  | 310876 => 265
  | 311142 => 226
  | 311369 => 169
  | _ => 0

private theorem part306539 : Segment Valid highEstimate e306539 e311539 := by
  apply gcd_batch (by decide) (by decide) extra306539 18
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [306539,311539). -/
theorem batch306539 :
    Segment Valid highEstimate
      ⟨306539, 306454995417763145, 306457397240772409, 617179685752607, 617187194586000⟩
      ⟨311539, 311264949902066446, 311267422545720665, 623502246523567, 623510040891681⟩ := by
  exact part306539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
