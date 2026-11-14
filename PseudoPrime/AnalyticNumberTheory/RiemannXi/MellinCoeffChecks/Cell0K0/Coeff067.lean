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
/-- The height-independent coefficient at index 67 is kernel checked. -/
theorem coeff067 :
    ((1 + (0 : ℚ) / 16) ^ 67)⁻¹ *
        (∑ l ∈ Finset.Icc (67 : ℕ) 71,
          ((l.factorial : ℚ)⁻¹ *
              (((1 + ((0 + 1 : ℕ) : ℚ) / 16) - (1 + (0 : ℚ) / 16)) ^ (l + 1) / (l + 1))) *
            (l.choose 67 : ℚ) *
            (-(314159265358979323846264338327950288419716939937510 / 10 ^ 50 : ℚ) *
                ((0 : ℚ) + 1) ^ 2) ^
              (l - 67)) =
      (2666939083033332321732511882693767047658168405901919699641593979971985895439503930772220626025773746882203863125332227266258162612421788618091152822843747345608073840589150737859671852850911514225964190894327 :
          ℚ) /
        60906638039586718807635804668108641680191617517923189925418884735821034973938053428982167253980358822199013544837333565984142270142196104178855249112648496926086723180345425920000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by
  decide +kernel

end PseudoPrime.AnalyticNumberTheory.RiemannXi.Coeff0K0
