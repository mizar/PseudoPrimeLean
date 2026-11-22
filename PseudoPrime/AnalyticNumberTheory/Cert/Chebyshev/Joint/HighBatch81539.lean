/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 81539 to 86539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e81539 : Edge :=
  ⟨81539, 81557656554439411, 81558397564588102, 340448479726655, 340452523982820⟩

private def e86539 : Edge :=
  ⟨86539, 86566559281221489, 86567344155290023, 348961863957856, 348966058918126⟩

private def extra81539 : ℕ → ℕ
  | 81539 => 167
  | 81707 => 193
  | 81901 => 137
  | 82039 => 153
  | 82193 => 155
  | 82349 => 149
  | 82499 => 119
  | 82619 => 143
  | 82763 => 139
  | 82903 => 173
  | 83077 => 179
  | 83257 => 173
  | 83431 => 177
  | 83609 => 203
  | 83813 => 239
  | 84053 => 209
  | 84263 => 199
  | 84463 => 209
  | 84673 => 239
  | 84913 => 219
  | 85133 => 229
  | 85363 => 228
  | 85592 => 204
  | 85797 => 215
  | 86013 => 182
  | 86196 => 181
  | 86378 => 160
  | _ => 0

private theorem part81539 : Segment Valid highEstimate e81539 e86539 := by
  apply gcd_batch (by decide) (by decide) extra81539 27
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [81539,86539). -/
theorem batch81539 :
    Segment Valid highEstimate
      ⟨81539, 81557656554439411, 81558397564588102, 340448479726655, 340452523982820⟩
      ⟨86539, 86566559281221489, 86567344155290023, 348961863957856, 348966058918126⟩ := by
  exact part81539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
