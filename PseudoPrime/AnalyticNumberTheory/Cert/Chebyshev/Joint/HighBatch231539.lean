/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 231539 to 236539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e231539 : Edge :=
  ⟨231539, 231745495560216332, 231747298600661942, 552982813167160, 552989211302836⟩

private def e236539 : Edge :=
  ⟨236539, 236480611358270303, 236482434983938771, 552982813167160, 552989211302836⟩

private def extra231539 : ℕ → ℕ
  | 231539 => 161
  | 231701 => 175
  | 231877 => 195
  | 232073 => 233
  | 232307 => 241
  | 232549 => 261
  | 232811 => 305
  | 233117 => 299
  | 233417 => 329
  | 233747 => 401
  | 234149 => 361
  | 234511 => 321
  | 234833 => 283
  | 235117 => 371
  | 235489 => 399
  | 235889 => 385
  | 236275 => 263
  | _ => 0

private theorem part231539 : Segment Valid highEstimate e231539 e236539 := by
  apply gcd_batch (by decide) (by decide) extra231539 17
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [231539,236539). -/
theorem batch231539 :
    Segment Valid highEstimate
      ⟨231539, 231745495560216332, 231747298600661942, 552982813167160, 552989211302836⟩
      ⟨236539, 236480611358270303, 236482434983938771, 552982813167160, 552989211302836⟩ := by
  exact part231539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
