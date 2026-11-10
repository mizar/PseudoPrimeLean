/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterInteriorCost
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterInteriorAbel
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterInteriorLower

/-! # Elementary interior large-index comparison -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH and the interior large-index no-witness hypotheses, the explicit
Chebyshev lower expression satisfies the principal-cost inequality. Combine
the joint Abel identity with the RH Chebyshev lower bound and the explicit
width-eight principal budget. -/
theorem quarter_interior_elementary {n : ℕ} [NeZero n] (hn : 1 < n) (ho : Odd n) {r T : ℝ}
    (hr : 4 ≤ r) (hbound : Real.log (r ^ 2) ≤ 16) (hT : 0 ≤ T) (hscale : Real.log n ≤ T)
    (hindex : 33000 ≤ (PrimeTest.fermatSubgroup n).index)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hnone :
      ¬∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n)) :
    ((48 - 2 * Real.log (r ^ 2)) * (r ^ 2) ^ (-1 / 2 : ℝ)) *
          (r ^ 2 - (19 / 30 : ℝ) * (r ^ 2) ^ (3 / 4 : ℝ) - (63 / 10 : ℝ) * (r ^ 2) ^ (1 / 4 : ℝ) -
            1839 / 1000) +
        (∫ t in (16 : ℝ)..(r ^ 2),
          (t ^ (-3 / 2 : ℝ) * (25 - Real.log (r ^ 2) / 2 - Real.log t / 2)) *
            (t - (19 / 30 : ℝ) * t ^ (3 / 4 : ℝ) - (63 / 10 : ℝ) * t ^ (1 / 4 : ℝ) - 1839 / 1000)) ≤
      (32 - Real.log (r ^ 2)) * T + (137 / 330 : ℝ) * (r + r⁻¹) +
        (4 / 15 : ℝ) * (Real.sqrt r + (Real.sqrt r)⁻¹) +
        15 / 11 := by
  have hr1 : 1 ≤ r := by linarith only [hr]
  have hX16 : (16 : ℝ) ≤ r ^ 2 := by nlinarith only [hr, sq_nonneg (r - 4)]
  have hX1 : (1 : ℝ) ≤ r ^ 2 := by linarith only [hX16]
  have hcost := quarter_interior_explicit_cost hn ho hr1 hbound hT hscale hindex hGRH hnone
  have hab :=
    quarter_interior_abel (a := 8) (X := r ^ 2) (by norm_num only) hX1 (by linarith only [hbound])
  have hlow :=
    quarter_interior_integral_lower hGRH.riemann (a := 12 - Real.log (r ^ 2) / 4) hX16
      (by linarith only [hbound])
  rw [intervalIntegral.integral_of_le (by linarith only [hX16] : (1 : ℝ) ≤ r ^ 2)] at hlow
  have hpsi := LLS.PaperStatements.scaleOne_psi_lower hGRH.riemann hX16
  have hc : 0 ≤ (48 - 2 * Real.log (r ^ 2)) * (r ^ 2) ^ (-1 / 2 : ℝ) :=
    mul_nonneg (by linarith only [hbound]) (Real.rpow_nonneg (sq_nonneg r) _)
  have hp := mul_le_mul_of_nonneg_left hpsi hc
  dsimp only at hcost
  norm_num only at hab hlow
  have he (t : ℝ) :
    2 * (12 - Real.log (r ^ 2) / 4) + 1 - Real.log t / 2 =
      25 - Real.log (r ^ 2) / 2 - Real.log t / 2 := by
    ring
  simp only [he] at hlow
  have he' (t : ℝ) :
    24 - Real.log (r ^ 2) / 2 + 1 - Real.log t / 2 =
      25 - Real.log (r ^ 2) / 2 - Real.log t / 2 := by
    ring
  simp only [he'] at hab
  linarith only [hcost, hab, hlow, hp]

end PseudoPrime.PrimeTestBounds.MillerRabin
