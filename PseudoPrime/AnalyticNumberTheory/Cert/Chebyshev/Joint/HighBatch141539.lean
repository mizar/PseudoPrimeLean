/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 141539 to 146539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e141539 : Edge :=
  ⟨141539, 141624410084419827, 141625553194246354, 428270569200360, 428275884536636⟩

private def e146539 : Edge :=
  ⟨146539, 146524007745593682, 146525211438669482, 434208105237132, 434213452403432⟩

private def extra141539 : ℕ → ℕ
  | 141539 => 169
  | 141709 => 153
  | 141863 => 167
  | 142031 => 151
  | 142183 => 185
  | 142369 => 197
  | 142567 => 203
  | 142771 => 207
  | 142979 => 277
  | 143257 => 261
  | 143519 => 271
  | 143791 => 281
  | 144073 => 328
  | 144402 => 273
  | 144676 => 284
  | 144961 => 273
  | 145235 => 249
  | 145485 => 249
  | 145735 => 285
  | 146021 => 296
  | 146318 => 220
  | _ => 0

private theorem part141539 : Segment Valid highEstimate e141539 e146539 := by
  apply gcd_batch (by decide) (by decide) extra141539 21
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [141539,146539). -/
theorem batch141539 :
    Segment Valid highEstimate
      ⟨141539, 141624410084419827, 141625553194246354, 428270569200360, 428275884536636⟩
      ⟨146539, 146524007745593682, 146525211438669482, 434208105237132, 434213452403432⟩ := by
  exact part141539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
