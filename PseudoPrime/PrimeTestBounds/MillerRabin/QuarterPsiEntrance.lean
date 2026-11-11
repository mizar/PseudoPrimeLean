/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPsiRowsLower

/-! # Chebyshev lower bound at the uniform interval entrance -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

-- Kernel reduction traverses the full filtered 39760 prime-power prefix.
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Kernel reduction checks the full filtered prime-power prefix.
private theorem anchor_rows : (39400 : ℚ) ≤ ((centerRowsBelow 39760).map (fun r ↦ r.lo)).sum := by
  decide +kernel

/-- The certified prime-power prefix gives an unconditional lower bound at 39760. -/
theorem psi_39760_lower : (39400 : ℝ) ≤ Chebyshev.psi 39760 := by
  exact quarter_psi_rows_lower (by decide) 39400 anchor_rows

/-- On the entrance interval, the certified prefix and monotonicity bound `psi` below. -/
theorem psi_lower_entrance {x : ℝ} (ha : 39760 ≤ x) (hb : x < 40000) :
    x - 600 ≤ Chebyshev.psi x := by
  have h := psi_39760_lower
  have hm := Chebyshev.psi_mono ha
  linarith only [h, hm, hb]

end PseudoPrime.PrimeTestBounds.MillerRabin
