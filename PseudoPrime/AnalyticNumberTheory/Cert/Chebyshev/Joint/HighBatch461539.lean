/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 461539 to 466539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e461539 : Edge :=
  ⟨461539, 461324724473296167, 461328128623490929, 771190383594335, 771200121195691⟩

private def e466539 : Edge :=
  ⟨466539, 466250265461667456, 466253696779499100, 777716877009608, 777726748583835⟩

private def extra461539 : ℕ → ℕ
  | 461539 => 328
  | 461868 => 260
  | 462129 => 234
  | 462364 => 182
  | 462547 => 207
  | 462755 => 260
  | 463016 => 208
  | 463225 => 130
  | 463356 => 182
  | 463539 => 207
  | 463747 => 182
  | 463930 => 221
  | 464152 => 247
  | 464400 => 247
  | 464648 => 260
  | 464909 => 274
  | 465184 => 403
  | 465588 => 352
  | 465941 => 312
  | 466254 => 284
  | _ => 0

private theorem part461539 : Segment Valid highEstimate e461539 e466539 := by
  apply gcd_batch (by decide) (by decide) extra461539 20
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [461539,466539). -/
theorem batch461539 :
    Segment Valid highEstimate
      ⟨461539, 461324724473296167, 461328128623490929, 771190383594335, 771200121195691⟩
      ⟨466539, 466250265461667456, 466253696779499100, 777716877009608, 777726748583835⟩ := by
  exact part461539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
