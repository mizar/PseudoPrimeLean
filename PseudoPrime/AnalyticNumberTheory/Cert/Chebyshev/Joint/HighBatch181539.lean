/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 181539 to 186539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e181539 : Edge :=
  ⟨181539, 181400821236517595, 181402347797528581, 483658631419302, 483664422362539⟩

private def e186539 : Edge :=
  ⟨186539, 186559095622921103, 186560655391780817, 489724738027783, 489730665251735⟩

private def extra181539 : ℕ → ℕ
  | 181539 => 201
  | 181741 => 181
  | 181923 => 193
  | 182117 => 242
  | 182360 => 253
  | 182614 => 266
  | 182881 => 278
  | 183160 => 266
  | 183427 => 266
  | 183694 => 302
  | 183997 => 266
  | 184264 => 278
  | 184543 => 254
  | 184798 => 266
  | 185065 => 266
  | 185332 => 302
  | 185635 => 291
  | 185927 => 283
  | 186211 => 269
  | 186481 => 57
  | _ => 0

private theorem part181539 : Segment Valid highEstimate e181539 e186539 := by
  apply gcd_batch (by decide) (by decide) extra181539 20
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [181539,186539). -/
theorem batch181539 :
    Segment Valid highEstimate
      ⟨181539, 181400821236517595, 181402347797528581, 483658631419302, 483664422362539⟩
      ⟨186539, 186559095622921103, 186560655391780817, 489724738027783, 489730665251735⟩ := by
  exact part181539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
