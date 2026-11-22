/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 66539 to 71539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e66539 : Edge :=
  ⟨66539, 66492899855141710, 66493451560970070, 297687483794043, 297690390601889⟩

private def e71539 : Edge :=
  ⟨71539, 71527462009707256, 71528092128377610, 306973203214881, 306976483863075⟩

private def extra66539 : ℕ → ℕ
  | 66539 => 156
  | 66696 => 133
  | 66830 => 143
  | 66974 => 167
  | 67142 => 166
  | 67309 => 189
  | 67499 => 211
  | 67711 => 189
  | 67901 => 185
  | 68087 => 223
  | 68311 => 202
  | 68514 => 178
  | 68693 => 155
  | 68849 => 155
  | 69005 => 157
  | 69163 => 156
  | 69320 => 144
  | 69465 => 145
  | 69611 => 111
  | 69723 => 77
  | 69801 => 66
  | 69868 => 89
  | 69958 => 66
  | 70025 => 77
  | 70103 => 66
  | 70170 => 89
  | 70260 => 122
  | 70383 => 122
  | 70506 => 123
  | 70630 => 133
  | 70764 => 100
  | 70865 => 89
  | 70955 => 122
  | 71078 => 133
  | 71212 => 134
  | 71347 => 167
  | 71515 => 23
  | _ => 0

private theorem part66539 : Segment Valid highEstimate e66539 e71539 := by
  apply gcd_batch (by decide) (by decide) extra66539 37
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [66539,71539). -/
theorem batch66539 :
    Segment Valid highEstimate
      ⟨66539, 66492899855141710, 66493451560970070, 297687483794043, 297690390601889⟩
      ⟨71539, 71527462009707256, 71528092128377610, 306973203214881, 306976483863075⟩ := by
  exact part66539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
