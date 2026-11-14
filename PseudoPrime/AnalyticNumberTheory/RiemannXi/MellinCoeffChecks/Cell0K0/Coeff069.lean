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
/-- The height-independent coefficient at index 69 is kernel checked. -/
theorem coeff069 :
    ((1 + (0 : ℚ) / 16) ^ 69)⁻¹ *
        (∑ l ∈ Finset.Icc (69 : ℕ) 71,
          ((l.factorial : ℚ)⁻¹ *
              (((1 + ((0 + 1 : ℕ) : ℚ) / 16) - (1 + (0 : ℚ) / 16)) ^ (l + 1) / (l + 1))) *
            (l.choose 69 : ℚ) *
            (-(314159265358979323846264338327950288419716939937510 / 10 ^ 50 : ℚ) *
                ((0 : ℚ) + 1) ^ 2) ^
              (l - 69)) =
      (1963381700638592962578502086740060223617445095747973108762891861040927911261655985245549896628022168227 :
          ℚ) /
        55369670945078835279668913334644219709265106834475627204926258850746395430852775844529242958163962565635466858943030514531038427401996458344413862829680451750987930163950387200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by
  decide +kernel

end PseudoPrime.AnalyticNumberTheory.RiemannXi.Coeff0K0
