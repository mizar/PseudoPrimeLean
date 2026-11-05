/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.TriangularCreditedComparison
public import PseudoPrime.LLS.PaperStatements.TriangularScaleOneAbel

/-! # Interior triangular witness with scale-one credit -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Under GRH and an explicit strict interior gap, extract a prime factor of the level
or a prime outside the subgroup. Insert the scale-one Abel lower bound into the signed
all-scale comparison; the upper support condition prevents extrapolation beyond exp 36. -/
theorem exists_prime_scaleOne_interior {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 1 < x)
    (hu : x ≤ Real.exp 36)
    (hgap :
      300000000 * (Real.sqrt x + Real.sqrt x⁻¹) +
          1300000 * (x ^ (1 / 4 : ℝ) + (x⁻¹) ^ (1 / 4 : ℝ)) +
          602600000 +
          ((H.index : ℝ) - 1) * ((36 + triangularKernelProfile 18 x) * Real.log q + 11964) <
        (H.index : ℝ) *
          ((220 - 4 * Real.log x + 4 * Real.exp (-18)) * Real.sqrt x -
                (4576 - 78 * Real.log x) * x ^ (1 / 4 : ℝ) +
              2104 -
            36 * Real.log q / (Real.sqrt x - 1))) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ x ∧ (p ∣ q ∨ ¬NumberTheory.residueInSubgroup q H p) := by
  apply exists_prime_credited_gap H hGRH hx
  have hp := scaleOne_finite_lower hGRH.riemann hx.le hu
  have hm := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg H.index)
  nlinarith only [hgap, hm]

end PseudoPrime.LLS.PaperStatements
