/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 236539 to 241539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e236539 : Edge :=
  ⟨236539, 236480611358270303, 236482434983938771, 552982813167160, 552989211302836⟩

private def e241539 : Edge :=
  ⟨241539, 241459179626994363, 241461027353903130, 565367520318279, 565374043686911⟩

private def extra236539 : ℕ → ℕ
  | 236539 => 329
  | 236869 => 309
  | 237179 => 349
  | 237529 => 259
  | 237789 => 235
  | 238025 => 234
  | 238260 => 285
  | 238546 => 309
  | 238856 => 297
  | 239154 => 272
  | 239427 => 272
  | 239700 => 284
  | 239985 => 285
  | 240271 => 321
  | 240593 => 272
  | 240866 => 272
  | 241139 => 285
  | 241425 => 113
  | _ => 0

private theorem part236539 : Segment Valid highEstimate e236539 e241539 := by
  apply gcd_batch (by decide) (by decide) extra236539 18
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [236539,241539). -/
theorem batch236539 :
    Segment Valid highEstimate
      ⟨236539, 236480611358270303, 236482434983938771, 552982813167160, 552989211302836⟩
      ⟨241539, 241459179626994363, 241461027353903130, 565367520318279, 565374043686911⟩ := by
  exact part236539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
