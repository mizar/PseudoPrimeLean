/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.ExplicitFiberEnergyThreshold
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! # A quantitative double-logarithm bound for the explicit prime threshold -/

public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- For P(u)=2^(2^u), log log P(u)=u log 2+log log 2.
Expand logarithms with u symbolic, avoiding evaluation of the tower.
This identity makes the subsequent starting threshold fully explicit. -/
theorem log_log_explicit_finite_fiber_threshold (u : ℕ) :
    Real.log (Real.log (explicitFiniteFiberPrimeThreshold u : ℝ)) =
      (u : ℝ) * Real.log 2 + Real.log (Real.log 2) := by
  have hpow : (0 : ℝ) < (2 ^ u : ℕ) := Nat.cast_pos.mpr (Nat.pow_pos (by decide : 0 < 2))
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num only)
  rw [explicitFiniteFiberPrimeThreshold, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow,
    Real.log_mul hpow.ne' hlog.ne', Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]

/-- Every p≥P(1388714689827) satisfies log log p≥387 billion.
Use the exact symbolic tower logarithm and rational bounds on log 2.
No natural-number tower is evaluated or enumerated. -/
theorem three_hundred_eighty_seven_billion_le_double_log_of_explicit_fiber_threshold {p : ℕ}
    (hlarge : explicitFiniteFiberPrimeThreshold (1388714689827) ≤ p) :
    (387000000000 : ℝ) ≤ Real.log (Real.log p) := by
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith only [Real.log_two_gt_d9]
  have hlog2p : (0 : ℝ) < Real.log 2 := lt_of_lt_of_le (by norm_num only) hlog2
  have hll := Real.log_le_log (by norm_num only : (0 : ℝ) < 1 / 2) hlog2
  rw [Real.log_div (by norm_num only : (1 : ℝ) ≠ 0) (by norm_num only : (2 : ℝ) ≠ 0),
    Real.log_one] at hll
  have hbase :
    (387000000000 : ℝ) ≤
      Real.log (Real.log (explicitFiniteFiberPrimeThreshold (1388714689827) : ℝ)) := by
    rw [log_log_explicit_finite_fiber_threshold]
    norm_num only [Nat.cast_pow, Nat.cast_ofNat]
    nlinarith only [hlog2, hll, Real.log_two_lt_d9]
  have hP := one_lt_explicit_finite_fiber_threshold (1388714689827)
  have hlogbase := Real.log_pos (Nat.one_lt_cast.mpr hP)
  have hmono := Real.log_le_log (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hP)) (Nat.cast_le.mpr hlarge)
  exact hbase.trans (Real.log_le_log hlogbase hmono)

/-- Every p≥P(283000007562) satisfies log log p≥100 billion. Use the
symbolic tower logarithm and coarse rational lower bounds on log 2. This is
the double-logarithm input for the 40/74 rational scale. -/
theorem one_hundred_billion_le_double_log_of_explicit_fiber_threshold {p : ℕ}
    (hlarge : explicitFiniteFiberPrimeThreshold 283000007562 ≤ p) :
    (100000000000 : ℝ) ≤ Real.log (Real.log p) := by
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith only [Real.log_two_gt_d9]
  have hlog2p : (0 : ℝ) < Real.log 2 := lt_of_lt_of_le (by norm_num only) hlog2
  have hll := Real.log_le_log (by norm_num only : (0 : ℝ) < 1 / 2) hlog2
  rw [Real.log_div (by norm_num only : (1 : ℝ) ≠ 0) (by norm_num only : (2 : ℝ) ≠ 0),
    Real.log_one] at hll
  have hbase :
    (100000000000 : ℝ) ≤
      Real.log (Real.log (explicitFiniteFiberPrimeThreshold 283000007562 : ℝ)) := by
    rw [log_log_explicit_finite_fiber_threshold]
    norm_num only [Nat.cast_pow, Nat.cast_ofNat]
    nlinarith only [hlog2, hll, Real.log_two_lt_d9]
  have hP := one_lt_explicit_finite_fiber_threshold 283000007562
  have hlogbase := Real.log_pos (Nat.one_lt_cast.mpr hP)
  have hmono := Real.log_le_log (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hP)) (Nat.cast_le.mpr hlarge)
  exact hbase.trans (Real.log_le_log hlogbase hmono)

/-- Every p≥P(242591045876) satisfies log log p≥100 billion. Expand the
symbolic tower logarithm and retain the rational lower bounds for log 2. -/
theorem one_hundred_billion_le_double_log_of_explicit_fiber_threshold_38_70 {p : ℕ}
    (hlarge : explicitFiniteFiberPrimeThreshold 242591045876 ≤ p) :
    (100000000000 : ℝ) ≤ Real.log (Real.log p) := by
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith only [Real.log_two_gt_d9]
  have hlog2p : (0 : ℝ) < Real.log 2 := lt_of_lt_of_le (by norm_num only) hlog2
  have hll := Real.log_le_log (by norm_num only : (0 : ℝ) < 1 / 2) hlog2
  rw [Real.log_div (by norm_num only : (1 : ℝ) ≠ 0) (by norm_num only : (2 : ℝ) ≠ 0),
    Real.log_one] at hll
  have hbase :
    (100000000000 : ℝ) ≤
      Real.log (Real.log (explicitFiniteFiberPrimeThreshold 242591045876 : ℝ)) := by
    rw [log_log_explicit_finite_fiber_threshold]
    norm_num only [Nat.cast_pow, Nat.cast_ofNat]
    nlinarith only [hlog2, hll, Real.log_two_lt_d9]
  have hP := one_lt_explicit_finite_fiber_threshold 242591045876
  have hlogbase := Real.log_pos (Nat.one_lt_cast.mpr hP)
  have hmono := Real.log_le_log (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hP)) (Nat.cast_le.mpr hlarge)
  exact hbase.trans (Real.log_le_log hlogbase hmono)

/-- Every p≥P(145000006050) satisfies log log p≥20 billion.
Use the symbolic tower logarithm and rational lower bounds for log 2. -/
theorem twenty_billion_le_double_log_of_explicit_fiber_threshold_32_59 {p : ℕ}
    (hlarge : explicitFiniteFiberPrimeThreshold 145000006050 ≤ p) :
    (20000000000 : ℝ) ≤ Real.log (Real.log p) := by
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith only [Real.log_two_gt_d9]
  have hlog2p : (0 : ℝ) < Real.log 2 := lt_of_lt_of_le (by norm_num only) hlog2
  have hll := Real.log_le_log (by norm_num only : (0 : ℝ) < 1 / 2) hlog2
  rw [Real.log_div (by norm_num only : (1 : ℝ) ≠ 0) (by norm_num only : (2 : ℝ) ≠ 0),
    Real.log_one] at hll
  have hbase :
    (20000000000 : ℝ) ≤
      Real.log (Real.log (explicitFiniteFiberPrimeThreshold 145000006050 : ℝ)) := by
    rw [log_log_explicit_finite_fiber_threshold]
    norm_num only [Nat.cast_pow, Nat.cast_ofNat]
    nlinarith only [hlog2, hll, Real.log_two_lt_d9]
  have hP := one_lt_explicit_finite_fiber_threshold 145000006050
  have hlogbase := Real.log_pos (Nat.one_lt_cast.mpr hP)
  have hmono := Real.log_le_log (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hP)) (Nat.cast_le.mpr hlarge)
  exact hbase.trans (Real.log_le_log hlogbase hmono)

/-- Every p≥P(4449271510) satisfies log log p≥2 billion. Expand the
symbolic tower logarithm and retain coarse rational bounds for log 2. -/
theorem two_billion_le_double_log_of_explicit_fiber_threshold_10_19 {p : ℕ}
    (hlarge : explicitFiniteFiberPrimeThreshold 4449271510 ≤ p) :
    (2000000000 : ℝ) ≤ Real.log (Real.log p) := by
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith only [Real.log_two_gt_d9]
  have hlog2p : (0 : ℝ) < Real.log 2 := lt_of_lt_of_le (by norm_num only) hlog2
  have hll := Real.log_le_log (by norm_num only : (0 : ℝ) < 1 / 2) hlog2
  rw [Real.log_div (by norm_num only : (1 : ℝ) ≠ 0) (by norm_num only : (2 : ℝ) ≠ 0),
    Real.log_one] at hll
  have hbase :
    (2000000000 : ℝ) ≤ Real.log (Real.log (explicitFiniteFiberPrimeThreshold 4449271510 : ℝ)) := by
    rw [log_log_explicit_finite_fiber_threshold]
    norm_num only [Nat.cast_pow, Nat.cast_ofNat]
    nlinarith only [hlog2, hll, Real.log_two_lt_d9]
  have hP := one_lt_explicit_finite_fiber_threshold 4449271510
  have hlogbase := Real.log_pos (Nat.one_lt_cast.mpr hP)
  have hmono := Real.log_le_log (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hP)) (Nat.cast_le.mpr hlarge)
  exact hbase.trans (Real.log_le_log hlogbase hmono)

/-- Every p≥P(4449271510) satisfies log log p≥3,084,000,000. The
nine-decimal lower bound for log 2 sharpens the double-log estimate while
leaving the finite-fiber starting parameter unchanged. -/
theorem three_billion_eighty_four_million_le_double_log_of_explicit_fiber_threshold_10_19 {p : ℕ}
    (hlarge : explicitFiniteFiberPrimeThreshold 4449271510 ≤ p) :
    (3084000000 : ℝ) ≤ Real.log (Real.log p) := by
  have hlog2 : (6931471803 / 10000000000 : ℝ) ≤ Real.log 2 := by linarith only [Real.log_two_gt_d9]
  have hlog2p : (0 : ℝ) < Real.log 2 := by linarith only [hlog2]
  have hll : -(1 : ℝ) ≤ Real.log (Real.log 2) := by
    have hhalf : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith only [hlog2]
    have hlog := Real.log_le_log (by norm_num only : (0 : ℝ) < 1 / 2) hhalf
    rw [Real.log_div (by norm_num only : (1 : ℝ) ≠ 0) (by norm_num only : (2 : ℝ) ≠ 0),
      Real.log_one] at hlog
    have hlog2lt1 : Real.log 2 ≤ 1 := by linarith only [Real.log_two_lt_d9]
    linarith only [hlog, hlog2lt1]
  have hbase :
    (3084000000 : ℝ) ≤ Real.log (Real.log (explicitFiniteFiberPrimeThreshold 4449271510 : ℝ)) := by
    rw [log_log_explicit_finite_fiber_threshold]
    norm_num only [Nat.cast_pow, Nat.cast_ofNat]
    nlinarith only [hlog2, hll]
  have hP := one_lt_explicit_finite_fiber_threshold 4449271510
  have hlogbase := Real.log_pos (Nat.one_lt_cast.mpr hP)
  have hmono := Real.log_le_log (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hP)) (Nat.cast_le.mpr hlarge)
  exact hbase.trans (Real.log_le_log hlogbase hmono)

/-- The refined 3.084-billion estimate implies the former 3.08-billion bound. -/
theorem three_billion_eighty_million_le_double_log_of_explicit_fiber_threshold_10_19 {p : ℕ}
    (hlarge : explicitFiniteFiberPrimeThreshold 4449271510 ≤ p) :
    (3080000000 : ℝ) ≤ Real.log (Real.log p) := by
  exact
    le_trans (by norm_num only)
      (three_billion_eighty_four_million_le_double_log_of_explicit_fiber_threshold_10_19 hlarge)

/-- The explicit 3.08-billion double-log estimate also implies the coarser
3-billion estimate used by the scale budget. -/
theorem three_billion_le_double_log_of_explicit_fiber_threshold_10_19 {p : ℕ}
    (hlarge : explicitFiniteFiberPrimeThreshold 4449271510 ≤ p) :
    (3000000000 : ℝ) ≤ Real.log (Real.log p) := by
  exact
    le_trans (by norm_num only)
      (three_billion_eighty_million_le_double_log_of_explicit_fiber_threshold_10_19 hlarge)

/-- Every p≥P(76598623) satisfies log log p≥53,000,000. This lower
bound supports the reduced starting parameter at scale 19/10. -/
theorem fifty_three_million_le_double_log_of_explicit_fiber_threshold {p u : ℕ} (hu : 76598623 ≤ u)
    (hlarge : explicitFiniteFiberPrimeThreshold u ≤ p) :
    (53000000 : ℝ) ≤ Real.log (Real.log p) := by
  have huR : (76598623 : ℝ) ≤ u := by exact_mod_cast hu
  have hlog2 : (6931471803 / 10000000000 : ℝ) ≤ Real.log 2 := by linarith only [Real.log_two_gt_d9]
  have hll : -(1 : ℝ) ≤ Real.log (Real.log 2) := by
    have hhalf : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith only [hlog2]
    have hlog := Real.log_le_log (by norm_num only : (0 : ℝ) < 1 / 2) hhalf
    rw [Real.log_div (by norm_num only : (1 : ℝ) ≠ 0) (by norm_num only : (2 : ℝ) ≠ 0),
      Real.log_one] at hlog
    have hlog2lt1 : Real.log 2 ≤ 1 := by linarith only [Real.log_two_lt_d9]
    linarith only [hlog, hlog2lt1]
  have hbase : (53000000 : ℝ) ≤ Real.log (Real.log (explicitFiniteFiberPrimeThreshold u : ℝ)) := by
    rw [log_log_explicit_finite_fiber_threshold]
    nlinarith only [huR, hlog2, hll]
  have hP := one_lt_explicit_finite_fiber_threshold u
  have hlogbase := Real.log_pos (Nat.one_lt_cast.mpr hP)
  have hmono := Real.log_le_log (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hP)) (Nat.cast_le.mpr hlarge)
  exact hbase.trans (Real.log_le_log hlogbase hmono)

/-- The reduced 19/10-scale prime threshold implies log log p≥14,900,000.
Use the symbolic logarithm of the double-exponential threshold and rational
bounds for log 2 and log log 2. -/
theorem fourteen_million_nine_hundred_thousand_le_double_log_of_explicit_fiber_threshold {p u : ℕ}
    (hu : 21518759 ≤ u) (hlarge : explicitFiniteFiberPrimeThreshold u ≤ p) :
    (14900000 : ℝ) ≤ Real.log (Real.log p) := by
  have huR : (21518759 : ℝ) ≤ u := by exact_mod_cast hu
  have hlog2 : (6931471803 / 10000000000 : ℝ) ≤ Real.log 2 := by linarith only [Real.log_two_gt_d9]
  have hll : -(1 : ℝ) ≤ Real.log (Real.log 2) := by
    have hhalf : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith only [hlog2]
    have hlog := Real.log_le_log (by norm_num only : (0 : ℝ) < 1 / 2) hhalf
    rw [Real.log_div (by norm_num only : (1 : ℝ) ≠ 0) (by norm_num only : (2 : ℝ) ≠ 0),
      Real.log_one] at hlog
    have hlog2lt1 : Real.log 2 ≤ 1 := by linarith only [Real.log_two_lt_d9]
    linarith only [hlog, hlog2lt1]
  have hbase : (14900000 : ℝ) ≤ Real.log (Real.log (explicitFiniteFiberPrimeThreshold u : ℝ)) := by
    rw [log_log_explicit_finite_fiber_threshold]
    nlinarith only [huR, hlog2, hll]
  have hP := one_lt_explicit_finite_fiber_threshold u
  have hlogbase := Real.log_pos (Nat.one_lt_cast.mpr hP)
  have hmono := Real.log_le_log (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hP)) (Nat.cast_le.mpr hlarge)
  exact hbase.trans (Real.log_le_log hlogbase hmono)

/-- Every p≥P(u) with u≥17,456,612 satisfies log log p≥12,100,000.
The explicit tower logarithm and rational bounds for log 2 and log log 2
give the lower bound uniformly in u. -/
theorem twelve_million_one_hundred_thousand_le_double_log_of_explicit_fiber_threshold {p u : ℕ}
    (hu : 17456612 ≤ u) (hlarge : explicitFiniteFiberPrimeThreshold u ≤ p) :
    (12100000 : ℝ) ≤ Real.log (Real.log p) := by
  have huR : (17456612 : ℝ) ≤ u := by exact_mod_cast hu
  have hlog2 : (6931471803 / 10000000000 : ℝ) ≤ Real.log 2 := by linarith only [Real.log_two_gt_d9]
  have hll : -(1 : ℝ) ≤ Real.log (Real.log 2) := by
    have hhalf : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith only [hlog2]
    have hlog := Real.log_le_log (by norm_num only : (0 : ℝ) < 1 / 2) hhalf
    rw [Real.log_div (by norm_num only : (1 : ℝ) ≠ 0) (by norm_num only : (2 : ℝ) ≠ 0),
      Real.log_one] at hlog
    have hlog2lt1 : Real.log 2 ≤ 1 := by linarith only [Real.log_two_lt_d9]
    linarith only [hlog, hlog2lt1]
  have hbase : (12100000 : ℝ) ≤ Real.log (Real.log (explicitFiniteFiberPrimeThreshold u : ℝ)) := by
    rw [log_log_explicit_finite_fiber_threshold]
    nlinarith only [huR, hlog2, hll]
  have hP := one_lt_explicit_finite_fiber_threshold u
  have hlogbase := Real.log_pos (Nat.one_lt_cast.mpr hP)
  have hmono := Real.log_le_log (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hP)) (Nat.cast_le.mpr hlarge)
  exact hbase.trans (Real.log_le_log hlogbase hmono)

/-- Every p≥P(u) with u≥17,431,511 satisfies log log p≥12,082,601.
The stronger threshold is sufficient for the 28/15 finite-fiber branch and is
derived from the symbolic tower logarithm without evaluating the tower. -/
theorem twelve_million_eighty_two_thousand_six_hundred_one_le_double_log_of_explicit_fiber_threshold
    {p u : ℕ} (hu : 17431511 ≤ u) (hlarge : explicitFiniteFiberPrimeThreshold u ≤ p) :
    (12082601 : ℝ) ≤ Real.log (Real.log p) := by
  have huR : (17431511 : ℝ) ≤ u := by exact_mod_cast hu
  have hlog2 : (6931471803 / 10000000000 : ℝ) ≤ Real.log 2 := by linarith only [Real.log_two_gt_d9]
  have hll : -(1 : ℝ) ≤ Real.log (Real.log 2) := by
    have hhalf : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith only [hlog2]
    have hlog := Real.log_le_log (by norm_num only : (0 : ℝ) < 1 / 2) hhalf
    rw [Real.log_div (by norm_num only : (1 : ℝ) ≠ 0) (by norm_num only : (2 : ℝ) ≠ 0),
      Real.log_one] at hlog
    have hlog2lt1 : Real.log 2 ≤ 1 := by linarith only [Real.log_two_lt_d9]
    linarith only [hlog, hlog2lt1]
  have hbase : (12082601 : ℝ) ≤ Real.log (Real.log (explicitFiniteFiberPrimeThreshold u : ℝ)) := by
    rw [log_log_explicit_finite_fiber_threshold]
    nlinarith only [huR, hlog2, hll]
  have hP := one_lt_explicit_finite_fiber_threshold u
  have hlogbase := Real.log_pos (Nat.one_lt_cast.mpr hP)
  have hmono := Real.log_le_log (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hP)) (Nat.cast_le.mpr hlarge)
  exact hbase.trans (Real.log_le_log hlogbase hmono)

/-- The threshold P(77001892) gives the sharper bound
log log p≥53,373,643, retaining the fractional part of the rational log-2
estimate. -/
theorem fifty_three_million_three_hundred_seventy_three_thousand_le_double_log {p : ℕ}
    (hlarge : explicitFiniteFiberPrimeThreshold 77001892 ≤ p) :
    (53373643 : ℝ) ≤ Real.log (Real.log p) := by
  have hlog2 : (6931471803 / 10000000000 : ℝ) ≤ Real.log 2 := by linarith only [Real.log_two_gt_d9]
  have hll : -(1 : ℝ) ≤ Real.log (Real.log 2) := by
    have hhalf : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith only [hlog2]
    have hlog := Real.log_le_log (by norm_num only : (0 : ℝ) < 1 / 2) hhalf
    rw [Real.log_div (by norm_num only : (1 : ℝ) ≠ 0) (by norm_num only : (2 : ℝ) ≠ 0),
      Real.log_one] at hlog
    have hlog2lt1 : Real.log 2 ≤ 1 := by linarith only [Real.log_two_lt_d9]
    linarith only [hlog, hlog2lt1]
  have hbase :
    (53373643 : ℝ) ≤ Real.log (Real.log (explicitFiniteFiberPrimeThreshold 77001892 : ℝ)) := by
    rw [log_log_explicit_finite_fiber_threshold]
    norm_num only [Nat.cast_pow, Nat.cast_ofNat]
    nlinarith only [hlog2, hll]
  have hP := one_lt_explicit_finite_fiber_threshold 77001892
  have hlogbase := Real.log_pos (Nat.one_lt_cast.mpr hP)
  have hmono := Real.log_le_log (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hP)) (Nat.cast_le.mpr hlarge)
  exact hbase.trans (Real.log_le_log hlogbase hmono)

/-- The tightened precision-20 coefficient threshold gives the sharper bound
log log p≥53,266,470, retaining the fractional part of the rational log-2
estimate. -/
theorem fifty_three_million_one_hundred_sixty_two_thousand_le_double_log {p : ℕ}
    (hlarge : explicitFiniteFiberPrimeThreshold 76697551 ≤ p) :
    (53162690 : ℝ) ≤ Real.log (Real.log p) := by
  have hlog2 : (6931471803 / 10000000000 : ℝ) ≤ Real.log 2 := by linarith only [Real.log_two_gt_d9]
  have hll : -(1 : ℝ) ≤ Real.log (Real.log 2) := by
    have hhalf : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith only [hlog2]
    have hlog := Real.log_le_log (by norm_num only : (0 : ℝ) < 1 / 2) hhalf
    rw [Real.log_div (by norm_num only : (1 : ℝ) ≠ 0) (by norm_num only : (2 : ℝ) ≠ 0),
      Real.log_one] at hlog
    have hlog2lt1 : Real.log 2 ≤ 1 := by linarith only [Real.log_two_lt_d9]
    linarith only [hlog, hlog2lt1]
  have hbase :
    (53162690 : ℝ) ≤ Real.log (Real.log (explicitFiniteFiberPrimeThreshold 76697551 : ℝ)) := by
    rw [log_log_explicit_finite_fiber_threshold]
    norm_num only [Nat.cast_pow, Nat.cast_ofNat]
    nlinarith only [hlog2, hll]
  have hP := one_lt_explicit_finite_fiber_threshold 76697551
  have hlogbase := Real.log_pos (Nat.one_lt_cast.mpr hP)
  have hmono := Real.log_le_log (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hP)) (Nat.cast_le.mpr hlarge)
  exact hbase.trans (Real.log_le_log hlogbase hmono)

end PseudoPrime.NumberTheory.Heilbronn
