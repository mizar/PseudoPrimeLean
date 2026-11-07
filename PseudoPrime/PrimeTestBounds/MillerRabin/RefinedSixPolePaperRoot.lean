/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPolePaperScalar

/-! # Positive root and scalar exclusion for the refined paper bound -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The positive quadratic root `s_K(L)` from the paper, with its exact constants.
Its fourth power is the proposed witness cutoff. -/
noncomputable def refinedPaperRoot (L K : ℝ) : ℝ :=
  ((53 / 500 : ℝ) +
      Real.sqrt
        ((53 / 500 : ℝ) ^ 2 + 4 * (24439 / 50000 : ℝ) * ((3 / (8 * (27 / 25 : ℝ) ^ 5)) * L + K))) /
    (2 * (24439 / 50000 : ℝ))

/-- The paper cutoff `B_K(L)`, the fourth power of its positive root. It supplies the
three piecewise high-range witness bounds for residual allowances `3`, `1` and `0`. -/
noncomputable def refinedPaperBound (L K : ℝ) : ℝ :=
  refinedPaperRoot L K ^ 4

/-- The paper root is positive for all real arguments. Its numerator is positive
because the square root is nonnegative, and its denominator is positive. -/
theorem refined_paper_root_positive (L K : ℝ) : 0 < refinedPaperRoot L K := by
  dsimp only [refinedPaperRoot]
  apply div_pos _ (by norm_num only)
  linarith only [Real.sqrt_nonneg
      ((53 / 500 : ℝ) ^ 2 + 4 * (24439 / 50000 : ℝ) * ((3 / (8 * (27 / 25 : ℝ) ^ 5)) * L + K))]

/-- For nonnegative `L` and `K`, the positive root solves the defining quadratic.
Square the nonnegative discriminant root and normalize the rational coefficients. -/
theorem refined_paper_root_equation {L K : ℝ} (hL : 0 ≤ L) (hK : 0 ≤ K) :
    (24439 / 50000 : ℝ) * refinedPaperRoot L K ^ 2 =
      (3 / (8 * (27 / 25 : ℝ) ^ 5)) * L + K + (53 / 500 : ℝ) * refinedPaperRoot L K := by
  have hd :
    0 ≤ (53 / 500 : ℝ) ^ 2 + 4 * (24439 / 50000 : ℝ) * ((3 / (8 * (27 / 25 : ℝ) ^ 5)) * L + K) := by
    positivity
  have hs := Real.sq_sqrt hd
  dsimp only [refinedPaperRoot]
  norm_num only at hs ⊢
  nlinarith only [hs]

/-- The square of the paper root solves the scalar boundary equation with its
positive square root. This form is used to contradict a strict necessary inequality. -/
theorem refined_root_strict_gap {L K : ℝ} (hL : 0 ≤ L) (hK : 0 ≤ K) :
    (24439 / 50000 : ℝ) * (refinedPaperRoot L K ^ 2) =
      (3 / (8 * (27 / 25 : ℝ) ^ 5)) * L + (53 / 500 : ℝ) * Real.sqrt (refinedPaperRoot L K ^ 2) +
        K := by
  rw [Real.sqrt_sq (refined_paper_root_positive L K).le]
  have h := refined_paper_root_equation hL hK
  linarith only [h]

/-- For nonnegative inputs, the paper root squared is at least `(261/500)L`.
Use its quadratic equation and positivity of its remaining terms. -/
theorem refined_root_lower {L K : ℝ} (hL : 0 ≤ L) (hK : 0 ≤ K) :
    (261 / 500 : ℝ) * L ≤ refinedPaperRoot L K ^ 2 := by
  have he := refined_paper_root_equation hL hK
  have hp := (refined_paper_root_positive L K).le
  norm_num only at he ⊢
  nlinarith only [he, hp, hL, hK]

/-- For `L ≥ 1000` and `0 ≤ K ≤ 3`, the paper root squared is at most `(57/100)L`.
Compare the quadratic at the square root of this linear cap. -/
theorem refined_root_upper {L K : ℝ} (hL : 1000 ≤ L) (hK : 0 ≤ K) (hK3 : K ≤ 3) :
    refinedPaperRoot L K ^ 2 ≤ (57 / 100 : ℝ) * L := by
  have hL0 : 0 ≤ L := by linarith only [hL]
  let z : ℝ := Real.sqrt ((57 / 100 : ℝ) * L)
  have hz0 : 0 ≤ z := Real.sqrt_nonneg _
  have hzsq : z ^ 2 = (57 / 100 : ℝ) * L := Real.sq_sqrt (mul_nonneg (by norm_num only) hL0)
  have hz20 : (20 : ℝ) ≤ z := by nlinarith only [hzsq, hz0, hL]
  have hzcap : z ≤ L / 40 := by
    have h :=
      (Real.sqrt_le_left (show (0 : ℝ) ≤ L / 40 by positivity)).mpr
        (show (57 / 100 : ℝ) * L ≤ (L / 40) ^ 2 by nlinarith only [hL, sq_nonneg (L - 1000)])
    exact h
  have he := refined_paper_root_equation hL0 hK
  have hp := refined_paper_root_positive L K
  have hzbudget :
    (3 / (8 * (27 / 25 : ℝ) ^ 5)) * L + K + (53 / 500 : ℝ) * z ≤ (24439 / 50000 : ℝ) * z ^ 2 := by
    norm_num only at ⊢
    nlinarith only [hzsq, hzcap, hL, hK3]
  have hs : refinedPaperRoot L K ≤ z := by
    by_contra hn
    have hd : 0 < refinedPaperRoot L K - z := sub_pos.mpr (lt_of_not_ge hn)
    have hm :=
      mul_pos hd
        (show 0 < (24439 / 50000 : ℝ) * (refinedPaperRoot L K + z) - 53 / 500 by
          nlinarith only [hp, hz20])
    norm_num only at he hzbudget hm
    nlinarith only [he, hzbudget, hm]
  have hsq := pow_le_pow_left₀ hp.le hs 2
  simpa only [hzsq] using hsq

/-- If the explicit residual at the paper root is at most its normalized allowance,
the strict scalar necessary condition is impossible. Multiply the root equation by
the positive kernel normalization and compare with the residual bound. -/
theorem refined_root_scalar_excludes {L K : ℝ} (hL : 0 ≤ L) (hK : 0 ≤ K)
    (hres : refinedPaperResidual L (refinedPaperRoot L K ^ 2) ≤ (27 / 25 : ℝ) ^ 5 * K) :
    ¬((27 / 25 : ℝ) ^ 5 * (24439 / 50000) * (refinedPaperRoot L K ^ 2) <
        (3 / 8 : ℝ) * L + (27 / 25 : ℝ) ^ 5 * (53 / 500) * Real.sqrt (refinedPaperRoot L K ^ 2) +
          refinedPaperResidual L (refinedPaperRoot L K ^ 2)) := by
  have he := refined_root_strict_gap hL hK
  have hm := congrArg (fun z : ℝ ↦ (27 / 25 : ℝ) ^ 5 * z) he
  norm_num only at hm ⊢
  linarith only [hm, hres]

end PseudoPrime.PrimeTestBounds.MillerRabin
