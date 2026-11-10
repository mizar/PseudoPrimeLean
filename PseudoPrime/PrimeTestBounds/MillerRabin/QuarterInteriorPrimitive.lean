/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterInteriorElementary
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterJointElementary

/-! # Primitive interior large-index comparison -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH and the interior large-index no-witness hypotheses, evaluating
the explicit joint Chebyshev integral gives the displayed endpoint inequality.
Apply the existing joint primitive to the interior weight; this reduces the
middle-range witness argument to a scalar comparison. -/
theorem quarter_interior_primitive {n : ℕ} [NeZero n] (hn : 1 < n) (ho : Odd n) {r T : ℝ}
    (hr : 4 ≤ r) (hbound : Real.log (r ^ 2) ≤ 16) (hT : 0 ≤ T) (hscale : Real.log n ≤ T)
    (hindex : 33000 ≤ (PrimeTest.fermatSubgroup n).index)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hnone :
      ¬∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n)) :
    ((48 - 2 * Real.log (r ^ 2)) * (r ^ 2) ^ (-1 / 2 : ℝ)) *
          (r ^ 2 - (19 / 30 : ℝ) * (r ^ 2) ^ (3 / 4 : ℝ) - (63 / 10 : ℝ) * (r ^ 2) ^ (1 / 4 : ℝ) -
            1839 / 1000) +
        (quarterJointPrimitive (12 - Real.log (r ^ 2) / 4) (r ^ 2) -
          quarterJointPrimitive (12 - Real.log (r ^ 2) / 4) 16) ≤
      (32 - Real.log (r ^ 2)) * T + (137 / 330 : ℝ) * (r + r⁻¹) +
        (4 / 15 : ℝ) * (Real.sqrt r + (Real.sqrt r)⁻¹) +
        15 / 11 := by
  have hX16 : (16 : ℝ) ≤ r ^ 2 := by nlinarith only [hr, sq_nonneg (r - 4)]
  have h := quarter_interior_elementary hn ho hr hbound hT hscale hindex hGRH hnone
  have he (t : ℝ) :
    25 - Real.log (r ^ 2) / 2 - Real.log t / 2 =
      2 * (12 - Real.log (r ^ 2) / 4) + 1 - Real.log t / 2 := by
    ring
  simp only [he] at h
  rw [quarter_joint_integral_eq (by norm_num only : (0 : ℝ) < 16) hX16] at h
  exact h

end PseudoPrime.PrimeTestBounds.MillerRabin
