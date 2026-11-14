/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountAbelBudget

/-! # Reciprocal zero sum with the height-100 head retained -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- A height-100 zero count and a continuous zero-count budget on
`[100,b]` bound the reciprocal sum over `(100,b]`. The upper-endpoint
count is retained for cancellation with the inverse-square tail. -/
theorem reciprocal_above100_retain_count {b : ℝ} {M E : ℝ → ℝ} (hb : 100 ≤ b)
    (h100 : zeroCount 100 = 58) (hM : ContinuousOn M (Set.Icc 100 b))
    (hE : ContinuousOn E (Set.Icc 100 b)) (hQ : ∀ t ∈ Set.Icc 100 b, |zeroCount t - M t| ≤ E t) :
    zeroReciprocalSum b - zeroReciprocalSum 100 ≤
      zeroCount b / b + (∫ t in (100 : ℝ)..b, M t / t ^ 2) + (∫ t in (100 : ℝ)..b, E t / t ^ 2) -
        58 / 100 := by
  have h := zeroReciprocal_abel (by norm_num only : (1 : ℝ) < 100) hb
  have hi := count_integral_le_of_error (by norm_num only : (0 : ℝ) < 100) hb hM hE hQ
  rw [h100] at h
  linarith only [h, hi]

/-- A height-100 zero count and reciprocal head bound, together with a
continuous counting budget on `[100,b]`, bound the reciprocal sum at `b`.
The exact count at `b` is kept for cancellation with the ordinate tail. -/
theorem reciprocal_sum_retain_count100 {b : ℝ} {M E : ℝ → ℝ} (hb : 100 ≤ b)
    (h100 : zeroCount 100 = 58) (hhead : zeroReciprocalSum 100 ≤ 11846 / 10000)
    (hM : ContinuousOn M (Set.Icc 100 b)) (hE : ContinuousOn E (Set.Icc 100 b))
    (hQ : ∀ t ∈ Set.Icc 100 b, |zeroCount t - M t| ≤ E t) :
    zeroReciprocalSum b ≤
      zeroCount b / b + (∫ t in (100 : ℝ)..b, M t / t ^ 2) + (∫ t in (100 : ℝ)..b, E t / t ^ 2) +
          11846 / 10000 -
        58 / 100 := by
  have h := zeroReciprocal_abel (by norm_num only : (1 : ℝ) < 100) hb
  have hi := count_integral_le_of_error (by norm_num only : (0 : ℝ) < 100) hb hM hE hQ
  rw [h100] at h
  linarith only [h, hi, hhead]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
