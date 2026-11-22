/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 131539 to 136539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e131539 : Edge :=
  ⟨131539, 131526568479638167, 131527599263438967, 416443632175696, 416448666166048⟩

private def e136539 : Edge :=
  ⟨136539, 136620934511478539, 136622021341265911, 422348991608372, 422354214641944⟩

private def extra131539 : ℕ → ℕ
  | 131539 => 274
  | 131814 => 283
  | 132098 => 247
  | 132346 => 247
  | 132594 => 248
  | 132843 => 273
  | 133117 => 261
  | 133379 => 289
  | 133669 => 296
  | 133966 => 247
  | 134214 => 271
  | 134486 => 282
  | 134769 => 238
  | 135008 => 224
  | 135233 => 224
  | 135458 => 248
  | 135707 => 307
  | 136015 => 272
  | 136288 => 230
  | 136519 => 19
  | _ => 0

private theorem part131539 : Segment Valid highEstimate e131539 e136539 := by
  apply gcd_batch (by decide) (by decide) extra131539 20
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [131539,136539). -/
theorem batch131539 :
    Segment Valid highEstimate
      ⟨131539, 131526568479638167, 131527599263438967, 416443632175696, 416448666166048⟩
      ⟨136539, 136620934511478539, 136622021341265911, 422348991608372, 422354214641944⟩ := by
  exact part131539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
