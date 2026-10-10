/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Integer series for quadratic decay and logarithmic height errors

A shifted p-series controls logarithmic quadratic weights. Finite tail estimates and
integer-bin denominator comparisons support uniform bounds for sums indexed by heights.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For x >= 0, a logarithmic quadratic-decay weight is bounded by ten times the
shifted three-halves power weight. Bound the logarithm by a square root and compare the
quadratic denominators. This explicit majorant proves summability of logarithmic height errors. -/
theorem logWeighted_quadratic_le_rpow {x : ℝ} (hx : 0 ≤ x) :
    (Real.log (4 + x) + 1) / (1 + x ^ 2) ≤ 10 / (1 + x) ^ (3 / 2 : ℝ) := by
  have hy : 0 < 1 + x := by linarith only [hx]
  have hd : 0 < 1 + x ^ 2 := by nlinarith only [sq_nonneg x]
  have hsq := Real.sq_sqrt hy.le
  have hsq4 := Real.sq_sqrt (show 0 ≤ 4 + x by linarith only [hx])
  have hs0 := Real.sqrt_nonneg (1 + x)
  have ht0 := Real.sqrt_nonneg (4 + x)
  have hs1 : 1 ≤ Real.sqrt (1 + x) := by nlinarith only [hsq, hs0, hx]
  have hroot : Real.sqrt (4 + x) ≤ 2 * Real.sqrt (1 + x) := by
    nlinarith only [hsq, hsq4, hs0, ht0, hx]
  have hl :=
    Real.log_le_rpow_div (show 0 ≤ 4 + x by linarith only [hx])
      (show (0 : ℝ) < 1 / 2 by norm_num only)
  rw [← Real.sqrt_eq_rpow] at hl
  have hn : Real.log (4 + x) + 1 ≤ 5 * Real.sqrt (1 + x) := by linarith only [hl, hroot, hs1]
  have hden : (1 + x) ^ 2 ≤ 2 * (1 + x ^ 2) := by nlinarith only [sq_nonneg (x - 1)]
  have hp : 0 < (1 + x) ^ 2 := pow_pos hy 2
  have hr : Real.sqrt (1 + x) / (1 + x) ^ 2 = 1 / (1 + x) ^ (3 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_two, ← Real.rpow_sub hy,
      show (1 / 2 : ℝ) - 2 = -(3 / 2 : ℝ) by norm_num only, Real.rpow_neg hy.le, one_div]
  calc
    _ ≤ (5 * Real.sqrt (1 + x)) / (1 + x ^ 2) := div_le_div_of_nonneg_right hn hd.le
    _ ≤ (10 * Real.sqrt (1 + x)) / (1 + x) ^ 2 := by
      rw [div_le_div_iff₀ hd hp]
      have hm := mul_le_mul_of_nonneg_left hden (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 5) hs0)
      nlinarith only [hm]
    _ = _ := by rw [mul_div_assoc, hr, ← mul_div_assoc, mul_one]

/-- For p > 1, the shifted absolute p-series over integers converges.
Split into nonnegative and negative integer indices and apply the shifted natural p-series.
This provides a positive majorant without a singular term at zero. -/
theorem summable_int_shifted_abs_rpow {p : ℝ} (hp : 1 < p) :
    Summable (fun k : ℤ ↦ 1 / (1 + |(k : ℝ)|) ^ p) := by
  have hn := (Real.summable_one_div_nat_add_rpow 1 p).mpr hp
  have hnat : Summable (fun n : ℕ ↦ 1 / (1 + (n : ℝ)) ^ p) :=
    hn.congr
      (fun n ↦ by
        rw [abs_of_nonneg
            (show 0 ≤ (n : ℝ) + 1 by linarith only [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]),
          add_comm])
  have hnabs : ∀ n : ℕ, |(n : ℝ)| = (n : ℝ) := fun n ↦ abs_of_nonneg (Nat.cast_nonneg n)
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · simpa only [Int.cast_natCast, hnabs] using hnat
  · simpa only [Int.cast_neg, Int.cast_natCast, abs_neg, hnabs] using hnat

/-- The integer series with numerator log(4+|k|)+1 and denominator 1+k^2 is summable.
The explicit three-halves power majorant and positivity give absolute convergence.
Its total sum supplies a conductor-independent error in zero-mass tail bounds. -/
theorem summable_int_logWeighted_quadratic :
    Summable (fun k : ℤ ↦ (Real.log (4 + |(k : ℝ)|) + 1) / (1 + (k : ℝ) ^ 2)) := by
  apply
    Summable.of_norm_bounded
      ((summable_int_shifted_abs_rpow (show (1 : ℝ) < 3 / 2 by norm_num only)).mul_left 10)
  intro k
  have hl0 : 0 ≤ Real.log (4 + |(k : ℝ)|) :=
    Real.log_nonneg (show 1 ≤ 4 + |(k : ℝ)| by linarith only [abs_nonneg (k : ℝ)])
  have hn : 0 ≤ (Real.log (4 + |(k : ℝ)|) + 1) / (1 + (k : ℝ) ^ 2) :=
    div_nonneg (by linarith only [hl0]) (by nlinarith only [sq_nonneg (k : ℝ)])
  rw [Real.norm_eq_abs, abs_of_nonneg hn, ← sq_abs]
  simpa only [← mul_div_assoc, mul_one] using logWeighted_quadratic_le_rpow (abs_nonneg (k : ℝ))

/-- The integer inverse-quadratic series is summable.
Compare it with the nonnegative summable logarithmic quadratic weight.
This is the conductor coefficient in finite height-bin estimates. -/
theorem summable_int_quadratic : Summable (fun k : ℤ ↦ 1 / (1 + (k : ℝ) ^ 2)) := by
  apply
    Summable.of_nonneg_of_le
      (fun k ↦ div_nonneg zero_le_one (by nlinarith only [sq_nonneg (k : ℝ)])) (fun k ↦ ?_)
      summable_int_logWeighted_quadratic
  have hl : 0 ≤ Real.log (4 + |(k : ℝ)|) := Real.log_nonneg (by linarith only [abs_nonneg (k : ℝ)])
  exact div_le_div_of_nonneg_right (by linarith only [hl]) (by nlinarith only [sq_nonneg (k : ℝ)])

/-- For every epsilon > 0, a finite integer set contains all but an epsilon-sized part
of the inverse-quadratic series, uniformly over finite sets disjoint from it.
Use the norm vanishing-tail criterion and nonnegativity of finite sums.
This selects a height cutoff for conductor-uniform kernel zero tails. -/
theorem exists_int_quadratic_finite_tail_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ I : Finset ℤ, ∀ J : Finset ℤ, Disjoint J I → ∑ k ∈ J, 1 / (1 + (k : ℝ) ^ 2) < ε := by
  obtain ⟨I, hI⟩ := summable_iff_vanishing_norm.mp summable_int_quadratic ε hε
  refine ⟨I, fun J hJ ↦ ?_⟩
  have hn : 0 ≤ ∑ k ∈ J, 1 / (1 + (k : ℝ) ^ 2) :=
    Finset.sum_nonneg (fun k _ ↦ div_nonneg zero_le_one (by nlinarith only [sq_nonneg (k : ℝ)]))
  simpa only [Real.norm_eq_abs, abs_of_nonneg hn] using hI J hJ

/-- Two real arguments at distance at most one have quadratic denominators comparable
with factor three. Bound the squared difference and expand a nonnegative square.
This transfers quadratic kernel decay to the integer height bin containing each zero. -/
theorem quadraticDenominator_le_of_dist_le_one {t u : ℝ} (h : |t - u| ≤ 1) :
    1 + u ^ 2 ≤ 3 * (1 + t ^ 2) := by
  have hu := (abs_le.mp h).2
  have hl := (abs_le.mp h).1
  have hs : (t - u) ^ 2 ≤ 1 := by nlinarith only [hu, hl]
  nlinarith only [hs, sq_nonneg (2 * t - u), sq_nonneg t]

/-- Every real number has distance at most one from its integer floor.
The lower and strict upper floor bounds give the absolute-value estimate.
This places each height bin inside a window where local zero counts apply. -/
theorem abs_sub_int_floor_le_one (t : ℝ) : |t - (⌊t⌋ : ℝ)| ≤ 1 := by
  have hl := Int.floor_le t
  have hu := Int.lt_floor_add_one t
  exact abs_le.mpr ⟨by linarith only [hl], by linarith only [hu]⟩

end PseudoPrime.Analysis
