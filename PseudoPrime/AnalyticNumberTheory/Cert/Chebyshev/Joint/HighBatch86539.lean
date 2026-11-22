/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 86539 to 91539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e86539 : Edge :=
  ⟨86539, 86566559281221489, 86567344155290023, 348961863957856, 348966058918126⟩

private def e91539 : Edge :=
  ⟨91539, 91524323397062698, 91525148737217362, 348961863957856, 348966058918126⟩

private def extra86539 : ℕ → ℕ
  | 86539 => 243
  | 86783 => 221
  | 87005 => 182
  | 87188 => 193
  | 87382 => 170
  | 87553 => 197
  | 87751 => 209
  | 87961 => 253
  | 88215 => 182
  | 88398 => 148
  | 88547 => 124
  | 88672 => 114
  | 88787 => 67
  | 88855 => 125
  | 88981 => 113
  | 89095 => 148
  | 89244 => 159
  | 89404 => 148
  | 89553 => 159
  | 89713 => 193
  | 89907 => 183
  | 90091 => 221
  | 90313 => 215
  | 90529 => 259
  | 90789 => 205
  | 90995 => 205
  | 91201 => 228
  | 91430 => 108
  | _ => 0

private theorem part86539 : Segment Valid highEstimate e86539 e91539 := by
  apply gcd_batch (by decide) (by decide) extra86539 28
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [86539,91539). -/
theorem batch86539 :
    Segment Valid highEstimate
      ⟨86539, 86566559281221489, 86567344155290023, 348961863957856, 348966058918126⟩
      ⟨91539, 91524323397062698, 91525148737217362, 348961863957856, 348966058918126⟩ := by
  exact part86539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
