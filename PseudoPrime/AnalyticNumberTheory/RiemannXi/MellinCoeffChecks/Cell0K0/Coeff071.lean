/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module
public import PseudoPrime.AnalyticNumberTheory.RiemannXi.CriticalMellinCoefficients

/-! One shared coefficient for a critical-line Mellin certificate. -/

set_option linter.style.longLine false

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannXi.Coeff0K0

set_option maxRecDepth 16384 in
set_option maxHeartbeats 16000000 in
-- Exact evaluation of the finite rational coefficient needs a larger budget.
/-- The height-independent coefficient at index 71 is kernel checked. -/
theorem coeff071 :
    ((1 + (0 : ℚ) / 16) ^ 71)⁻¹ *
        (∑ l ∈ Finset.Icc (71 : ℕ) 71,
          ((l.factorial : ℚ)⁻¹ *
              (((1 + ((0 + 1 : ℕ) : ℚ) / 16) - (1 + (0 : ℚ) / 16)) ^ (l + 1) / (l + 1))) *
            (l.choose 71 : ℚ) *
            (-(314159265358979323846264338327950288419716939937510 / 10 ^ 50 : ℚ) *
                ((0 : ℚ) + 1) ^ 2) ^
              (l - 71)) =
      (1 : ℚ) /
        30453319019793359403817902334054320840095808758961594962709442367910517486969026714491083626990179411099506772418666782992071135071098052089427624556324248463043361590172712960000000000000000 := by
  decide +kernel

end PseudoPrime.AnalyticNumberTheory.RiemannXi.Coeff0K0
