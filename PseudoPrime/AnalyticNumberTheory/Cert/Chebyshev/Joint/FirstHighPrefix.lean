/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.Band3500
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.HighBatch3500

/-! # First high prefix -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

/-- The first high batch extends both square-root estimates from the 3500 prefix. -/
theorem first_high_prefix :
    Valid ⟨6539, 6525660194961613, 6525735033785668, 99186924014031, 99187319472619⟩ ∧
      ∀ x : ℝ, 3500 ≤ x → x < 6539 → highEstimate x := by
  exact batch3500 prefix3500.1

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
