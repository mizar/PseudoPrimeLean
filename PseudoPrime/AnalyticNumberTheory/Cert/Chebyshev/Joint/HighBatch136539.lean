/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 136539 to 141539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e136539 : Edge :=
  ⟨136539, 136620934511478539, 136622021341265911, 422348991608372, 422354214641944⟩

private def e141539 : Edge :=
  ⟨141539, 141624410084419827, 141625553194246354, 428270569200360, 428275884536636⟩

private def extra136539 : ℕ → ℕ
  | 136539 => 199
  | 136739 => 211
  | 136951 => 225
  | 137177 => 205
  | 137383 => 209
  | 137593 => 237
  | 137831 => 245
  | 138077 => 241
  | 138319 => 227
  | 138547 => 191
  | 138739 => 219
  | 138959 => 307
  | 139267 => 233
  | 139501 => 237
  | 139739 => 247
  | 139987 => 261
  | 140249 => 227
  | 140477 => 205
  | 140683 => 183
  | 140867 => 211
  | 141079 => 197
  | 141277 => 219
  | 141497 => 41
  | _ => 0

private theorem part136539 : Segment Valid highEstimate e136539 e141539 := by
  apply gcd_batch (by decide) (by decide) extra136539 23
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [136539,141539). -/
theorem batch136539 :
    Segment Valid highEstimate
      ⟨136539, 136620934511478539, 136622021341265911, 422348991608372, 422354214641944⟩
      ⟨141539, 141624410084419827, 141625553194246354, 428270569200360, 428275884536636⟩ := by
  exact part136539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
