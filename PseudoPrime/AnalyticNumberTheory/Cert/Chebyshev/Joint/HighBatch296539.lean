/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 296539 to 301539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e296539 : Edge :=
  ⟨296539, 296300504889641223, 296302817040882213, 606670545532904, 606677924376081⟩

private def e301539 : Edge :=
  ⟨301539, 301278727200321726, 301281083501084600, 617179685752607, 617187194586000⟩

private def extra296539 : ℕ → ℕ
  | 296539 => 196
  | 296736 => 238
  | 296975 => 252
  | 297228 => 213
  | 297442 => 188
  | 297631 => 214
  | 297846 => 188
  | 298035 => 188
  | 298224 => 201
  | 298426 => 188
  | 298615 => 138
  | 298754 => 150
  | 298905 => 151
  | 299057 => 112
  | 299170 => 100
  | 299271 => 94
  | 299366 => 112
  | 299479 => 138
  | 299618 => 113
  | 299732 => 125
  | 299858 => 87
  | 299946 => 88
  | 300035 => 100
  | 300136 => 62
  | 300199 => 87
  | 300287 => 75
  | 300363 => 100
  | 300464 => 87
  | 300552 => 75
  | 300628 => 87
  | 300716 => 100
  | 300817 => 155
  | 300973 => 176
  | 301150 => 150
  | 301301 => 151
  | 301453 => 85
  | _ => 0

private theorem part296539 : Segment Valid highEstimate e296539 e301539 := by
  apply gcd_batch (by decide) (by decide) extra296539 36
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [296539,301539). -/
theorem batch296539 :
    Segment Valid highEstimate
      ⟨296539, 296300504889641223, 296302817040882213, 606670545532904, 606677924376081⟩
      ⟨301539, 301278727200321726, 301281083501084600, 617179685752607, 617187194586000⟩ := by
  exact part296539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
