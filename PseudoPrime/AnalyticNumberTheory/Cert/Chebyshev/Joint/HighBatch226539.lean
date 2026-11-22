/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 226539 to 231539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e226539 : Edge :=
  ⟨226539, 226564048406585613, 226565830273712052, 542700239780932, 542706527944601⟩

private def e231539 : Edge :=
  ⟨231539, 231745495560216332, 231747298600661942, 552982813167160, 552989211302836⟩

private def extra226539 : ℕ → ℕ
  | 226539 => 331
  | 226871 => 361
  | 227233 => 333
  | 227567 => 379
  | 227947 => 381
  | 228329 => 317
  | 228647 => 281
  | 228929 => 293
  | 229223 => 283
  | 229507 => 231
  | 229739 => 199
  | 229939 => 177
  | 230117 => 173
  | 230291 => 139
  | 230431 => 131
  | 230563 => 179
  | 230743 => 147
  | 230891 => 139
  | 231031 => 237
  | 231269 => 191
  | 231461 => 77
  | _ => 0

private theorem part226539 : Segment Valid highEstimate e226539 e231539 := by
  apply gcd_batch (by decide) (by decide) extra226539 21
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [226539,231539). -/
theorem batch226539 :
    Segment Valid highEstimate
      ⟨226539, 226564048406585613, 226565830273712052, 542700239780932, 542706527944601⟩
      ⟨231539, 231745495560216332, 231747298600661942, 552982813167160, 552989211302836⟩ := by
  exact part226539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
