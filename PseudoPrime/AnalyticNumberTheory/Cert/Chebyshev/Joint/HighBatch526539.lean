/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighKernel

/-! # Joint high batch from 526539 to 531539 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private def e526539 : Edge :=
  ⟨526539, 526766214191606998, 526769855324902447, 809011830404582, 809022224396958⟩

private def e531539 : Edge :=
  ⟨531539, 531702746726333935, 531706404388295137, 816699368866669, 816709810119861⟩

private def extra526539 : ℕ → ℕ
  | 526539 => 291
  | 526831 => 291
  | 527123 => 275
  | 527399 => 301
  | 527701 => 311
  | 528013 => 369
  | 528383 => 407
  | 528791 => 361
  | 529153 => 365
  | 529519 => 413
  | 529933 => 345
  | 530279 => 323
  | 530603 => 293
  | 530897 => 331
  | 531229 => 309
  | _ => 0

private theorem part526539 : Segment Valid highEstimate e526539 e531539 := by
  apply gcd_batch (by decide) (by decide) extra526539 15
  decide +kernel

/-- The batch transports the prefix and proves both real bounds on [526539,531539). -/
theorem batch526539 :
    Segment Valid highEstimate
      ⟨526539, 526766214191606998, 526769855324902447, 809011830404582, 809022224396958⟩
      ⟨531539, 531702746726333935, 531706404388295137, 816699368866669, 816709810119861⟩ := by
  exact part526539

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
