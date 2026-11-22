/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 21539 to 26539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e21539 : Edge :=
  ⟨21539, 21517387920455064, 21517611333191912, 171201049835284, 171202440239984⟩

private def e26539 : Edge :=
  ⟨26539, 26527428612908453, 26527688716979515, 189645814688954, 189647453908190⟩

private def extra21539 : ℕ → ℕ
  | 21539 => 91
  | 21631 => 120
  | 21752 => 109
  | 21862 => 120
  | 21983 => 99
  | 22083 => 75
  | 22159 => 111
  | 22271 => 97
  | 22369 => 111
  | 22481 => 125
  | 22607 => 100
  | 22708 => 98
  | 22807 => 99
  | 22907 => 109
  | 23017 => 63
  | 23081 => 85
  | 23167 => 83
  | 23251 => 81
  | 23333 => 113
  | 23447 => 115
  | 23563 => 105
  | 23669 => 91
  | 23761 => 71
  | 23833 => 75
  | 23909 => 71
  | 23981 => 61
  | 24043 => 53
  | 24097 => 23
  | 24121 => 15
  | 24137 => 31
  | 24169 => 27
  | 24197 => 31
  | 24229 => 21
  | 24251 => 65
  | 24317 => 71
  | 24389 => 79
  | 24469 => 63
  | 24533 => 97
  | 24631 => 117
  | 24749 => 127
  | 24877 => 111
  | 24989 => 131
  | 25121 => 111
  | 25233 => 101
  | 25335 => 101
  | 25437 => 101
  | 25539 => 91
  | 25631 => 101
  | 25733 => 112
  | 25846 => 101
  | 25948 => 122
  | 26071 => 111
  | 26183 => 122
  | 26306 => 116
  | 26423 => 115
  | _ => 0

private theorem part21539 : Segment Valid highEstimate e21539 e26539 := by
  apply gcd_batch (by decide) (by decide) extra21539 55
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [21539,26539). -/
theorem batch21539 :
    Segment Valid highEstimate
      ⟨21539, 21517387920455064, 21517611333191912, 171201049835284, 171202440239984⟩
      ⟨26539, 26527428612908453, 26527688716979515, 189645814688954, 189647453908190⟩ := by
  exact part21539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
