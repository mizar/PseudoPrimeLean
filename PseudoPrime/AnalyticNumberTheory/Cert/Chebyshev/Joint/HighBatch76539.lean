/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 76539 to 81539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e76539 : Edge :=
  ⟨76539, 76516825709496550, 76517511241989268, 318170025089659, 318173836614825⟩

private def e81539 : Edge :=
  ⟨81539, 81557656554439411, 81558397564588102, 340448479726655, 340452523982820⟩

private def extra76539 : ℕ → ℕ
  | 76539 => 196
  | 76736 => 179
  | 76916 => 180
  | 77097 => 168
  | 77266 => 169
  | 77436 => 179
  | 77616 => 166
  | 77783 => 199
  | 77983 => 207
  | 78191 => 238
  | 78430 => 191
  | 78622 => 203
  | 78826 => 202
  | 79029 => 158
  | 79188 => 169
  | 79358 => 180
  | 79539 => 157
  | 79697 => 203
  | 79901 => 203
  | 80105 => 169
  | 80275 => 214
  | 80490 => 192
  | 80683 => 214
  | 80898 => 172
  | 81071 => 167
  | 81239 => 169
  | 81409 => 129
  | _ => 0

private theorem part76539 : Segment Valid highEstimate e76539 e81539 := by
  apply gcd_batch (by decide) (by decide) extra76539 27
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [76539,81539). -/
theorem batch76539 :
    Segment Valid highEstimate
      ⟨76539, 76516825709496550, 76517511241989268, 318170025089659, 318173836614825⟩
      ⟨81539, 81557656554439411, 81558397564588102, 340448479726655, 340452523982820⟩ := by
  exact part76539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
