/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 126539 to 131539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e126539 : Edge :=
  ⟨126539, 126551028502105041, 126552040056599293, 406922726210478, 406927562467084⟩

private def e131539 : Edge :=
  ⟨131539, 131526568479638167, 131527599263438967, 416443632175696, 416448666166048⟩

private def extra126539 : ℕ → ℕ
  | 126539 => 287
  | 126827 => 289
  | 127117 => 211
  | 127329 => 235
  | 127565 => 187
  | 127753 => 282
  | 128036 => 246
  | 128283 => 223
  | 128507 => 281
  | 128789 => 259
  | 129049 => 243
  | 129293 => 235
  | 129529 => 233
  | 129763 => 279
  | 130043 => 263
  | 130307 => 223
  | 130531 => 251
  | 130783 => 279
  | 131063 => 301
  | 131365 => 173
  | _ => 0

private theorem part126539 : Segment Valid highEstimate e126539 e131539 := by
  apply gcd_batch (by decide) (by decide) extra126539 20
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [126539,131539). -/
theorem batch126539 :
    Segment Valid highEstimate
      ⟨126539, 126551028502105041, 126552040056599293, 406922726210478, 406927562467084⟩
      ⟨131539, 131526568479638167, 131527599263438967, 416443632175696, 416448666166048⟩ := by
  exact part126539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
