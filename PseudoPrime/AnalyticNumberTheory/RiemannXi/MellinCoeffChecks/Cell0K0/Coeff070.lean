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
/-- The height-independent coefficient at index 70 is kernel checked. -/
theorem coeff070 :
    ((1 + (0 : ℚ) / 16) ^ 70)⁻¹ *
        (∑ l ∈ Finset.Icc (70 : ℕ) 71,
          ((l.factorial : ℚ)⁻¹ *
              (((1 + ((0 + 1 : ℕ) : ℚ) / 16) - (1 + (0 : ℚ) / 16)) ^ (l + 1) / (l + 1))) *
            (l.choose 70 : ℚ) *
            (-(314159265358979323846264338327950288419716939937510 / 10 ^ 50 : ℚ) *
                ((0 : ℚ) + 1) ^ 2) ^
              (l - 70)) =
      (10402541115286950504693754980819208233169103837003 : ℚ) /
        341022609404180956369741347525804264726716783415023459828773150816467161108275775078287610604593274480397612233131766886809307223640515700889447083497471987268122750169907200000000000000000000000000000000000000000000000000000000000000000 := by
  decide +kernel

end PseudoPrime.AnalyticNumberTheory.RiemannXi.Coeff0K0
