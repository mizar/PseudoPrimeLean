/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028LogMoments

/-! # Checked logarithmic moment bounds through degree six -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

-- The rational checks evaluate logarithmic Taylor and power certificates.
set_option maxRecDepth 1000000 in
-- Reduction checks both turning-point endpoints for this moment.
/-- The 1th logarithmic moment is at most its Gamma integral plus the two
certified turning-point bounds. -/
theorem target028_log_moment_1_bound :
    (∑' n : ℕ, target028LogMoment 1 n) ≤ (1 : ℝ) / (29 / 50 : ℝ) ^ 2 + 2 * (232 / 1000 : ℝ) := by
  have hlogA :=
    Analysis.rationalLogIntervalCheck_sound
      (show Analysis.rationalLogIntervalCheck 1 0 32 (-2 / 10000) (2 / 10000) = true from by
        decide +kernel)
  have hpA :=
    AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
      (show
        AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 1 0 (1000001 / 1000000) 79 50 =
          true
        from by decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div, Rat.cast_neg, Set.mem_Icc] at hlogA hpA
  have hlogB :=
    Analysis.rationalLogIntervalCheck_sound
      (show Analysis.rationalLogIntervalCheck 2 1 32 (6929 / 10000) (6934 / 10000) = true from by
        decide +kernel)
  have hpB :=
    AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
      (show
        AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 2 0 (334483 / 1000000) 79 50 =
          true
        from by decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div, Rat.cast_neg, Set.mem_Icc] at hlogB hpB
  have h :=
    target028_log_moment_sum_bound 0 1 (by decide) (C := (232 / 1000 : ℝ))
      (by
        norm_num only; linarith only [hlogA.2])
      (by
        norm_num only; linarith only [hlogB.1])
      (by
        norm_num only [Nat.reduceAdd, Nat.cast_one, target028LogMoment, Real.log_one, pow_one,
          zero_mul, zero_le])
      (by
        have ht := target028_log_moment_point 1 2 hlogB.2 hpB.2
        norm_num only at ht ⊢
        linarith only [ht])
  norm_num only [Nat.reduceAdd, Nat.factorial, Nat.cast_ofNat] at h ⊢
  exact h

-- The rational checks evaluate logarithmic Taylor and power certificates.
set_option maxRecDepth 1000000 in
-- Reduction checks both turning-point endpoints for this moment.
/-- The 2th logarithmic moment is at most its Gamma integral plus the two
certified turning-point bounds. -/
theorem target028_log_moment_2_bound :
    (∑' n : ℕ, target028LogMoment 2 n) ≤ (2 : ℝ) / (29 / 50 : ℝ) ^ 3 + 2 * (216 / 1000 : ℝ) := by
  have hlogA :=
    Analysis.rationalLogIntervalCheck_sound
      (show Analysis.rationalLogIntervalCheck 3 2 32 (10984 / 10000) (10989 / 10000) = true from by
        decide +kernel)
  have hpA :=
    AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
      (show
        AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 3 0 (176259 / 1000000) 79 50 =
          true
        from by decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div, Rat.cast_neg, Set.mem_Icc] at hlogA hpA
  have hlogB :=
    Analysis.rationalLogIntervalCheck_sound
      (show Analysis.rationalLogIntervalCheck 4 2 32 (13860 / 10000) (13865 / 10000) = true from by
        decide +kernel)
  have hpB :=
    AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
      (show
        AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 4 0 (111880 / 1000000) 79 50 =
          true
        from by decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div, Rat.cast_neg, Set.mem_Icc] at hlogB hpB
  have h :=
    target028_log_moment_sum_bound 1 3 (by decide) (C := (216 / 1000 : ℝ))
      (by
        norm_num only; linarith only [hlogA.2])
      (by
        norm_num only; linarith only [hlogB.1])
      (by
        have ht := target028_log_moment_point 2 3 hlogA.2 hpA.2
        norm_num only at ht ⊢
        linarith only [ht])
      (by
        have ht := target028_log_moment_point 2 4 hlogB.2 hpB.2
        norm_num only at ht ⊢
        linarith only [ht])
  norm_num only [Nat.reduceAdd, Nat.factorial, Nat.cast_ofNat] at h ⊢
  exact h

-- The rational checks evaluate logarithmic Taylor and power certificates.
set_option maxRecDepth 1000000 in
-- Reduction checks both turning-point endpoints for this moment.
/-- The 3th logarithmic moment is at most its Gamma integral plus the two
certified turning-point bounds. -/
theorem target028_log_moment_3_bound :
    (∑' n : ℕ, target028LogMoment 3 n) ≤ (6 : ℝ) / (29 / 50 : ℝ) ^ 4 + 2 * (341 / 1000 : ℝ) := by
  have hlogA :=
    Analysis.rationalLogIntervalCheck_sound
      (show Analysis.rationalLogIntervalCheck 6 3 32 (17915 / 10000) (17920 / 10000) = true from by
        decide +kernel)
  have hpA :=
    AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
      (show
        AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 6 0 (58957 / 1000000) 79 50 =
          true
        from by decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div, Rat.cast_neg, Set.mem_Icc] at hlogA hpA
  have hlogB :=
    Analysis.rationalLogIntervalCheck_sound
      (show Analysis.rationalLogIntervalCheck 7 3 32 (19457 / 10000) (19462 / 10000) = true from by
        decide +kernel)
  have hpB :=
    AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
      (show
        AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 7 0 (46212 / 1000000) 79 50 =
          true
        from by decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div, Rat.cast_neg, Set.mem_Icc] at hlogB hpB
  have h :=
    target028_log_moment_sum_bound 2 6 (by decide) (C := (341 / 1000 : ℝ))
      (by
        norm_num only; linarith only [hlogA.2])
      (by
        norm_num only; linarith only [hlogB.1])
      (by
        have ht := target028_log_moment_point 3 6 hlogA.2 hpA.2
        norm_num only at ht ⊢
        linarith only [ht])
      (by
        have ht := target028_log_moment_point 3 7 hlogB.2 hpB.2
        norm_num only at ht ⊢
        linarith only [ht])
  norm_num only [Nat.reduceAdd, Nat.factorial, Nat.cast_ofNat] at h ⊢
  exact h

-- The rational checks evaluate logarithmic Taylor and power certificates.
set_option maxRecDepth 1000000 in
-- Reduction checks both turning-point endpoints for this moment.
/-- The 4th logarithmic moment is at most its Gamma integral plus the two
certified turning-point bounds. -/
theorem target028_log_moment_4_bound :
    (∑' n : ℕ, target028LogMoment 4 n) ≤ (24 : ℝ) / (29 / 50 : ℝ) ^ 5 + 2 * (753 / 1000 : ℝ) := by
  have hlogA :=
    Analysis.rationalLogIntervalCheck_sound
      (show Analysis.rationalLogIntervalCheck 12 4 32 (24847 / 10000) (24852 / 10000) = true from by
        decide +kernel)
  have hpA :=
    AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
      (show
        AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 12 0 (19721 / 1000000) 79 50 =
          true
        from by decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div, Rat.cast_neg, Set.mem_Icc] at hlogA hpA
  have hlogB :=
    Analysis.rationalLogIntervalCheck_sound
      (show Analysis.rationalLogIntervalCheck 13 4 32 (25647 / 10000) (25652 / 10000) = true from by
        decide +kernel)
  have hpB :=
    AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
      (show
        AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 13 0 (17378 / 1000000) 79 50 =
          true
        from by decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div, Rat.cast_neg, Set.mem_Icc] at hlogB hpB
  have h :=
    target028_log_moment_sum_bound 3 12 (by decide) (C := (753 / 1000 : ℝ))
      (by
        norm_num only; linarith only [hlogA.2])
      (by
        norm_num only; linarith only [hlogB.1])
      (by
        have ht := target028_log_moment_point 4 12 hlogA.2 hpA.2
        norm_num only at ht ⊢
        linarith only [ht])
      (by
        have ht := target028_log_moment_point 4 13 hlogB.2 hpB.2
        norm_num only at ht ⊢
        linarith only [ht])
  norm_num only [Nat.reduceAdd, Nat.factorial, Nat.cast_ofNat] at h ⊢
  exact h

-- The rational checks evaluate logarithmic Taylor and power certificates.
set_option maxRecDepth 1000000 in
-- Reduction checks both turning-point endpoints for this moment.
/-- The 5th logarithmic moment is at most its Gamma integral plus the two
certified turning-point bounds. -/
theorem target028_log_moment_5_bound :
    (∑' n : ℕ, target028LogMoment 5 n) ≤ (120 : ℝ) / (29 / 50 : ℝ) ^ 6 + 2 * (2140 / 1000 : ℝ) := by
  have hlogA :=
    Analysis.rationalLogIntervalCheck_sound
      (show Analysis.rationalLogIntervalCheck 23 5 32 (31352 / 10000) (31357 / 10000) = true from by
        decide +kernel)
  have hpA :=
    AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
      (show
        AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 23 0 (7056 / 1000000) 79 50 =
          true
        from by decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div, Rat.cast_neg, Set.mem_Icc] at hlogA hpA
  have hlogB :=
    Analysis.rationalLogIntervalCheck_sound
      (show Analysis.rationalLogIntervalCheck 24 5 32 (31778 / 10000) (31783 / 10000) = true from by
        decide +kernel)
  have hpB :=
    AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
      (show
        AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 24 0 (6597 / 1000000) 79 50 =
          true
        from by decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div, Rat.cast_neg, Set.mem_Icc] at hlogB hpB
  have h :=
    target028_log_moment_sum_bound 4 23 (by decide) (C := (2140 / 1000 : ℝ))
      (by
        norm_num only; linarith only [hlogA.2])
      (by
        norm_num only; linarith only [hlogB.1])
      (by
        have ht := target028_log_moment_point 5 23 hlogA.2 hpA.2
        norm_num only at ht ⊢
        linarith only [ht])
      (by
        have ht := target028_log_moment_point 5 24 hlogB.2 hpB.2
        norm_num only at ht ⊢
        linarith only [ht])
  norm_num only [Nat.reduceAdd, Nat.factorial, Nat.cast_ofNat] at h ⊢
  exact h

-- The rational checks evaluate logarithmic Taylor and power certificates.
set_option maxRecDepth 1000000 in
-- Reduction checks both turning-point endpoints for this moment.
/-- The 6th logarithmic moment is at most its Gamma integral plus the two
certified turning-point bounds. -/
theorem target028_log_moment_6_bound :
    (∑' n : ℕ, target028LogMoment 6 n) ≤ (720 : ℝ) / (29 / 50 : ℝ) ^ 7 + 2 * (7443 / 1000 : ℝ) := by
  have hlogA :=
    Analysis.rationalLogIntervalCheck_sound
      (show Analysis.rationalLogIntervalCheck 44 5 32 (37839 / 10000) (37844 / 10000) = true from by
        decide +kernel)
  have hpA :=
    AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
      (show
        AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 44 0 (2533 / 1000000) 79 50 =
          true
        from by decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div, Rat.cast_neg, Set.mem_Icc] at hlogA hpA
  have hlogB :=
    Analysis.rationalLogIntervalCheck_sound
      (show Analysis.rationalLogIntervalCheck 45 5 32 (38064 / 10000) (38069 / 10000) = true from by
        decide +kernel)
  have hpB :=
    AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
      (show
        AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 45 0 (2445 / 1000000) 79 50 =
          true
        from by decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div, Rat.cast_neg, Set.mem_Icc] at hlogB hpB
  have h :=
    target028_log_moment_sum_bound 5 44 (by decide) (C := (7443 / 1000 : ℝ))
      (by
        norm_num only; linarith only [hlogA.2])
      (by
        norm_num only; linarith only [hlogB.1])
      (by
        have ht := target028_log_moment_point 6 44 hlogA.2 hpA.2
        norm_num only at ht ⊢
        linarith only [ht])
      (by
        have ht := target028_log_moment_point 6 45 hlogB.2 hpB.2
        norm_num only at ht ⊢
        linarith only [ht])
  norm_num only [Nat.reduceAdd, Nat.factorial, Nat.cast_ofNat] at h ⊢
  exact h

end PseudoPrime.PrimeTestBounds.MillerRabin
