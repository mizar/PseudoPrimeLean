/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 156539 to 161539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e156539 : Edge :=
  ⟨156539, 156595255550532633, 156596572739483630, 450090008633458, 450095613867576⟩

private def e161539 : Edge :=
  ⟨161539, 161579996956010881, 161581356023361584, 464465800923861, 464471490629316⟩

private def extra156539 : ℕ → ℕ
  | 156539 => 241
  | 156781 => 267
  | 157049 => 209
  | 157259 => 173
  | 157433 => 203
  | 157637 => 203
  | 157841 => 229
  | 158071 => 269
  | 158341 => 249
  | 158591 => 271
  | 158863 => 315
  | 159179 => 311
  | 159491 => 277
  | 159769 => 263
  | 160033 => 285
  | 160319 => 307
  | 160627 => 249
  | 160877 => 259
  | 161137 => 269
  | 161407 => 131
  | _ => 0

private theorem part156539 : Segment Valid highEstimate e156539 e161539 := by
  apply gcd_batch (by decide) (by decide) extra156539 20
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [156539,161539). -/
theorem batch156539 :
    Segment Valid highEstimate
      ⟨156539, 156595255550532633, 156596572739483630, 450090008633458, 450095613867576⟩
      ⟨161539, 161579996956010881, 161581356023361584, 464465800923861, 464471490629316⟩ := by
  exact part156539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
