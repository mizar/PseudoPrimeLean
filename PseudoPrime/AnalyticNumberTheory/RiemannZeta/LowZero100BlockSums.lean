/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100PhaseArithmetic

/-! # Block decomposition of endpoint approximations -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The 127 power terms split into eight consecutive blocks followed by the correction.
The identity holds for every rational ordinate and lets independent kernel checks cover the
entire finite sum without a single large reduction. -/
theorem endpoint_finite_blocks (t : ℚ) :
    endpointFiniteApprox t =
      (endpointFiniteBlock t 1 17 + endpointFiniteBlock t 17 33 + endpointFiniteBlock t 33 49 +
          endpointFiniteBlock t 49 65 +
          endpointFiniteBlock t 65 81 +
          endpointFiniteBlock t 81 97 +
          endpointFiniteBlock t 97 113 +
          endpointFiniteBlock t 113 128) +
        endpointFiniteCorrection t := by
  simp only [endpointFiniteApprox, Analysis.rationalComplexAdd, endpointFiniteBlock]
  change
    (∑ n ∈ Finset.Icc (1 : ℕ) 127, endpointPowerApprox t (gridLogApprox n)) +
        endpointFiniteCorrection t =
      _
  rw [←
    show Finset.Ico (1 : ℕ) 128 = Finset.Icc 1 127 by exact Finset.Ico_add_one_right_eq_Icc 1 127]
  rw [←
    Finset.sum_Ico_consecutive _ (show 1 ≤ 113 by norm_num only) (show 113 ≤ 128 by norm_num only)]
  rw [←
    Finset.sum_Ico_consecutive _ (show 1 ≤ 97 by norm_num only) (show 97 ≤ 113 by norm_num only)]
  rw [← Finset.sum_Ico_consecutive _ (show 1 ≤ 81 by norm_num only) (show 81 ≤ 97 by norm_num only)]
  rw [← Finset.sum_Ico_consecutive _ (show 1 ≤ 65 by norm_num only) (show 65 ≤ 81 by norm_num only)]
  rw [← Finset.sum_Ico_consecutive _ (show 1 ≤ 49 by norm_num only) (show 49 ≤ 65 by norm_num only)]
  rw [← Finset.sum_Ico_consecutive _ (show 1 ≤ 33 by norm_num only) (show 33 ≤ 49 by norm_num only)]
  rw [← Finset.sum_Ico_consecutive _ (show 1 ≤ 17 by norm_num only) (show 17 ≤ 33 by norm_num only)]

/-- The real component of a rational product distributes over addition of pairs. This
allows the rotated block bounds to be summed with exact rational arithmetic. -/
theorem endpoint_rotated_add (p a b : ℚ × ℚ) :
    (Analysis.rationalComplexMul p (a + b)).1 =
      (Analysis.rationalComplexMul p a).1 + (Analysis.rationalComplexMul p b).1 := by
  simp only [Analysis.rationalComplexMul, Prod.fst_add, Prod.snd_add]
  ring

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
