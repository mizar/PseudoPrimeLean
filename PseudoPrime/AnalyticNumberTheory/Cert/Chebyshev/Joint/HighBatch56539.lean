/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 56539 to 61539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e56539 : Edge :=
  ⟨56539, 56557371116941355, 56557880493476111, 273859936122240, 273862672658375⟩

private def e61539 : Edge :=
  ⟨61539, 61556418269392894, 61556951470195781, 285919808194029, 285922634206487⟩

private def extra56539 : ℕ → ℕ
  | 56539 => 173
  | 56713 => 177
  | 56891 => 145
  | 57037 => 111
  | 57149 => 101
  | 57251 => 97
  | 57349 => 117
  | 57467 => 133
  | 57601 => 125
  | 57727 => 101
  | 57829 => 113
  | 57943 => 113
  | 58057 => 95
  | 58153 => 75
  | 58229 => 91
  | 58321 => 81
  | 58403 => 49
  | 58453 => 89
  | 58543 => 87
  | 58631 => 95
  | 58727 => 161
  | 58889 => 121
  | 59011 => 95
  | 59107 => 89
  | 59197 => 65
  | 59263 => 93
  | 59357 => 59
  | 59417 => 49
  | 59467 => 41
  | 59509 => 51
  | 59561 => 59
  | 59621 => 41
  | 59663 => 35
  | 59699 => 43
  | 59743 => 35
  | 59779 => 29
  | 59809 => 69
  | 59879 => 91
  | 59971 => 105
  | 60077 => 71
  | 60149 => 101
  | 60251 => 91
  | 60343 => 105
  | 60449 => 157
  | 60607 => 119
  | 60727 => 131
  | 60859 => 93
  | 60953 => 137
  | 61091 => 169
  | 61261 => 201
  | 61463 => 75
  | _ => 0

private theorem part56539 : Segment Valid highEstimate e56539 e61539 := by
  apply gcd_batch (by decide) (by decide) extra56539 51
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [56539,61539). -/
theorem batch56539 :
    Segment Valid highEstimate
      ⟨56539, 56557371116941355, 56557880493476111, 273859936122240, 273862672658375⟩
      ⟨61539, 61556418269392894, 61556951470195781, 285919808194029, 285922634206487⟩ := by
  exact part56539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
