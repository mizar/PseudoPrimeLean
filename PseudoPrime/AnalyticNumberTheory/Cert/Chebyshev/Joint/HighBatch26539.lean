/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 26539 to 31539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e26539 : Edge :=
  ⟨26539, 26527428612908453, 26527688716979515, 189645814688954, 189647453908190⟩

private def e31539 : Edge :=
  ⟨31539, 31490795457507930, 31491082208347120, 211009782613755, 211011781826428⟩

private def extra26539 : ℕ → ℕ
  | 26539 => 124
  | 26664 => 92
  | 26757 => 105
  | 26863 => 95
  | 26959 => 101
  | 27061 => 117
  | 27179 => 119
  | 27299 => 144
  | 27444 => 102
  | 27547 => 102
  | 27650 => 71
  | 27722 => 60
  | 27783 => 102
  | 27886 => 113
  | 28000 => 122
  | 28123 => 143
  | 28267 => 82
  | 28350 => 92
  | 28443 => 91
  | 28535 => 72
  | 28608 => 102
  | 28711 => 101
  | 28813 => 107
  | 28921 => 105
  | 29027 => 125
  | 29153 => 115
  | 29269 => 117
  | 29387 => 113
  | 29501 => 127
  | 29629 => 131
  | 29761 => 138
  | 29900 => 113
  | 30014 => 92
  | 30107 => 82
  | 30190 => 103
  | 30294 => 102
  | 30397 => 93
  | 30491 => 72
  | 30564 => 92
  | 30657 => 61
  | 30719 => 82
  | 30802 => 51
  | 30854 => 83
  | 30938 => 82
  | 31021 => 72
  | 31094 => 82
  | 31177 => 82
  | 31260 => 124
  | 31385 => 113
  | 31499 => 39
  | _ => 0

private theorem part26539 : Segment Valid highEstimate e26539 e31539 := by
  apply gcd_batch (by decide) (by decide) extra26539 50
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [26539,31539). -/
theorem batch26539 :
    Segment Valid highEstimate
      ⟨26539, 26527428612908453, 26527688716979515, 189645814688954, 189647453908190⟩
      ⟨31539, 31490795457507930, 31491082208347120, 211009782613755, 211011781826428⟩ := by
  exact part26539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
