/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 31539 to 36539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e31539 : Edge :=
  ⟨31539, 31490795457507930, 31491082208347120, 211009782613755, 211011781826428⟩

private def e36539 : Edge :=
  ⟨36539, 36515041254833651, 36515384263520497, 227341083034046, 227343370272661⟩

private def extra31539 : ℕ → ℕ
  | 31539 => 84
  | 31624 => 83
  | 31708 => 82
  | 31791 => 82
  | 31874 => 72
  | 31947 => 31
  | 31979 => 30
  | 32010 => 41
  | 32052 => 30
  | 32083 => 61
  | 32145 => 62
  | 32208 => 62
  | 32271 => 61
  | 32333 => 72
  | 32406 => 93
  | 32500 => 104
  | 32605 => 124
  | 32730 => 125
  | 32856 => 124
  | 32981 => 114
  | 33096 => 126
  | 33223 => 129
  | 33353 => 139
  | 33493 => 107
  | 33601 => 111
  | 33713 => 83
  | 33797 => 73
  | 33871 => 69
  | 33941 => 97
  | 34039 => 131
  | 34171 => 125
  | 34297 => 105
  | 34403 => 107
  | 34511 => 95
  | 34607 => 85
  | 34693 => 69
  | 34763 => 85
  | 34849 => 99
  | 34949 => 131
  | 35081 => 119
  | 35201 => 121
  | 35323 => 123
  | 35447 => 121
  | 35569 => 177
  | 35747 => 119
  | 35867 => 126
  | 35994 => 136
  | 36131 => 147
  | 36279 => 136
  | 36416 => 115
  | 36532 => 6
  | _ => 0

private theorem part31539 : Segment Valid highEstimate e31539 e36539 := by
  apply gcd_batch (by decide) (by decide) extra31539 51
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [31539,36539). -/
theorem batch31539 :
    Segment Valid highEstimate
      ⟨31539, 31490795457507930, 31491082208347120, 211009782613755, 211011781826428⟩
      ⟨36539, 36515041254833651, 36515384263520497, 227341083034046, 227343370272661⟩ := by
  exact part31539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
