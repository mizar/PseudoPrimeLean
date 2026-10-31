/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.SignedDivisionBounds

public import PseudoPrime.LLS.GammaSignedWindowTransport

/-! # Rational root enclosures for signed window allowances -/

@[expose] public section

namespace PseudoPrime.LLS
end PseudoPrime.LLS

namespace PseudoPrime.LLS

/-- Input: rational-compatible root bounds on an ordered window.
Claim: replacing the actual roots by those bounds enlarges the local excess
allowance. Apply the signed quotient comparison at both endpoints.
Role: verify interval sums using exact rational arithmetic. -/
theorem gamma_window_excess_le_root_bounds {lo hi a b e N : ℝ} (ha : 0 < a) (hlohi : lo ≤ hi)
    (hlo : a ≤ Real.sqrt lo) (hhi : Real.sqrt hi ≤ b) :
    gammaRamifiedWindowExcessBound lo hi e N ≤ max (e + max (N / a) (N / b)) 0 := by
  have hl :=
    Analysis.gamma_div_le_max_of_interval (v := N) ha hlo ((Real.sqrt_le_sqrt hlohi).trans hhi)
  have hh :=
    Analysis.gamma_div_le_max_of_interval (v := N) ha (hlo.trans (Real.sqrt_le_sqrt hlohi)) hhi
  exact max_le_max (add_le_add le_rfl (max_le hl hh)) le_rfl

end PseudoPrime.LLS
