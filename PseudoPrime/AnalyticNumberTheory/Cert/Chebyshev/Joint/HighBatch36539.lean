/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 36539 to 41539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e36539 : Edge :=
  ⟨36539, 36515041254833651, 36515384263520497, 227341083034046, 227343370272661⟩

private def e41539 : Edge :=
  ⟨41539, 41499131825914016, 41499532330518635, 243180280503640, 243182711459752⟩

private def extra36539 : ℕ → ℕ
  | 36539 => 119
  | 36659 => 131
  | 36791 => 121
  | 36913 => 105
  | 37019 => 119
  | 37139 => 133
  | 37273 => 123
  | 37397 => 119
  | 37517 => 73
  | 37591 => 71
  | 37663 => 119
  | 37783 => 113
  | 37897 => 141
  | 38039 => 161
  | 38201 => 131
  | 38333 => 177
  | 38511 => 115
  | 38627 => 95
  | 38723 => 137
  | 38861 => 137
  | 38999 => 137
  | 39137 => 137
  | 39275 => 133
  | 39409 => 153
  | 39563 => 158
  | 39722 => 137
  | 39860 => 148
  | 40009 => 143
  | 40153 => 164
  | 40318 => 137
  | 40456 => 95
  | 40552 => 116
  | 40669 => 95
  | 40765 => 85
  | 40851 => 105
  | 40957 => 106
  | 41064 => 106
  | 41171 => 95
  | 41267 => 148
  | 41416 => 122
  | _ => 0

private theorem part36539 : Segment Valid highEstimate e36539 e41539 := by
  apply gcd_batch (by decide) (by decide) extra36539 40
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [36539,41539). -/
theorem batch36539 :
    Segment Valid highEstimate
      ⟨36539, 36515041254833651, 36515384263520497, 227341083034046, 227343370272661⟩
      ⟨41539, 41499131825914016, 41499532330518635, 243180280503640, 243182711459752⟩ := by
  exact part36539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
