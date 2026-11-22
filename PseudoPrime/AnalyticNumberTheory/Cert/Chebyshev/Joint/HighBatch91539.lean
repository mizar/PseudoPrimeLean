/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 91539 to 96539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e91539 : Edge :=
  ⟨91539, 91524323397062698, 91525148737217362, 348961863957856, 348966058918126⟩

private def e96539 : Edge :=
  ⟨96539, 96648815437795990, 96649678592660318, 354688711387439, 354692955040586⟩

private def extra91539 : ℕ → ℕ
  | 91539 => 223
  | 91763 => 182
  | 91946 => 171
  | 92118 => 171
  | 92290 => 182
  | 92473 => 225
  | 92699 => 167
  | 92867 => 209
  | 93077 => 179
  | 93257 => 169
  | 93427 => 153
  | 93581 => 229
  | 93811 => 197
  | 94009 => 219
  | 94229 => 209
  | 94439 => 173
  | 94613 => 197
  | 94811 => 197
  | 95009 => 181
  | 95191 => 147
  | 95339 => 139
  | 95479 => 137
  | 95617 => 129
  | 95747 => 125
  | 95873 => 113
  | 95987 => 149
  | 96137 => 131
  | 96269 => 161
  | 96431 => 107
  | _ => 0

private theorem part91539 : Segment Valid highEstimate e91539 e96539 := by
  apply gcd_batch (by decide) (by decide) extra91539 29
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [91539,96539). -/
theorem batch91539 :
    Segment Valid highEstimate
      ⟨91539, 91524323397062698, 91525148737217362, 348961863957856, 348966058918126⟩
      ⟨96539, 96648815437795990, 96649678592660318, 354688711387439, 354692955040586⟩ := by
  exact part91539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
