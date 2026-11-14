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
/-- The height-independent coefficient at index 66 is kernel checked. -/
theorem coeff066 :
    ((1 + (0 : ℚ) / 16) ^ 66)⁻¹ *
        (∑ l ∈ Finset.Icc (66 : ℕ) 71,
          ((l.factorial : ℚ)⁻¹ *
              (((1 + ((0 + 1 : ℕ) : ℚ) / 16) - (1 + (0 : ℚ) / 16)) ^ (l + 1) / (l + 1))) *
            (l.choose 66 : ℚ) *
            (-(314159265358979323846264338327950288419716939937510 / 10 ^ 50 : ℚ) *
                ((0 : ℚ) + 1) ^ 2) ^
              (l - 66)) =
      (145087175432742014614607310798026628545286668250635195439444644626980693685306501215816230723493618651663376232556658317378864872395001970428984713720409754641751970334920857918509136147103172855031285665783739324205209654309794804107417156525613460280363511341 :
          ℚ) /
        3045331901979335940381790233405432084009580875896159496270944236791051748696902671449108362699017941109950677241866678299207113507109805208942762455632424846304336159017271296000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by
  decide +kernel

end PseudoPrime.AnalyticNumberTheory.RiemannXi.Coeff0K0
