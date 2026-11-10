/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.IntegratedZeroLedger

/-! # Bounds for the integrated trivial-zero correction

Control the correction by the inverse-square decay of its logarithmic series.
-/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- For `1 < x ≤ y`, the logarithmic trivial-zero series is nonincreasing.
Compare the inverse powers term by term in the summable series. -/
theorem triv_mono {x y : ℝ} (hx : 1 < x) (hxy : x ≤ y) :
    riemannZetaLogTrivialZeroSeries y ≤ riemannZetaLogTrivialZeroSeries x := by
  have hy : 1 < y := lt_of_lt_of_le hx hxy
  rw [riemannZetaLogTrivialZeroSeries, riemannZetaLogTrivialZeroSeries]
  apply Summable.tsum_le_tsum _ (summable_logTrivialZeroTerm hy) (summable_logTrivialZeroTerm hx)
  intro k
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hy0 : 0 < y := lt_of_lt_of_le hx0 hxy
  have hinv : y⁻¹ ≤ x⁻¹ := (inv_le_inv₀ hy0 hx0).2 hxy
  have hp := pow_le_pow_left₀ (inv_nonneg.mpr hy0.le) hinv (2 * (k + 1))
  exact div_le_div_of_nonneg_right hp (mul_nonneg (by norm_num only) (sq_nonneg ((k : ℝ) + 1)))

/-- The logarithmic trivial-zero series is nonnegative at every `x > 1`.
Each term is a quotient of nonnegative real numbers. -/
theorem triv_nonneg {x : ℝ} (hx : 1 < x) : 0 ≤ riemannZetaLogTrivialZeroSeries x := by
  rw [riemannZetaLogTrivialZeroSeries]
  apply tsum_nonneg
  intro k
  exact
    div_nonneg (pow_nonneg (inv_nonneg.mpr (zero_lt_one.trans hx).le) _)
      (mul_nonneg (by norm_num only) (sq_nonneg ((k : ℝ) + 1)))

/-- For `x > 1`, the trivial-zero series is at most `π² / (24x²)`.
Extract the first inverse-square factor and compare with the Basel series. -/
theorem triv_decay {x : ℝ} (hx : 1 < x) :
    riemannZetaLogTrivialZeroSeries x ≤ x⁻¹ ^ 2 * (Real.pi ^ 2 / 24) := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hi0 : 0 ≤ x⁻¹ := inv_nonneg.mpr hx0.le
  have hi1 : x⁻¹ ≤ 1 := (inv_le_one₀ hx0).2 hx.le
  have hb : Summable (fun k : ℕ ↦ (1 : ℝ) / ((k : ℝ) + 1) ^ 2) := by
    have h := hasSum_zeta_two.summable.comp_injective Nat.succ_injective
    change Summable (fun k : ℕ ↦ (1 : ℝ) / ((k + 1 : ℕ) : ℝ) ^ 2) at h
    simpa only [Nat.cast_add, Nat.cast_one] using h
  have hs := hb.mul_left (x⁻¹ ^ 2 / 4)
  have hterm (k : ℕ) :
    x⁻¹ ^ (2 * (k + 1)) / (4 * ((k : ℝ) + 1) ^ 2) ≤ (x⁻¹ ^ 2 / 4) * (1 / ((k : ℝ) + 1) ^ 2) := by
    have hp : x⁻¹ ^ (2 * (k + 1)) ≤ x⁻¹ ^ 2 := by
      rw [show 2 * (k + 1) = 2 + 2 * k by ring, pow_add]
      exact mul_le_of_le_one_right (sq_nonneg _) (pow_le_one₀ hi0 hi1)
    have h :=
      div_le_div_of_nonneg_right hp
        (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 4) (sq_nonneg ((k : ℝ) + 1)))
    calc
      _ ≤ x⁻¹ ^ 2 / (4 * ((k : ℝ) + 1) ^ 2) := h
      _ = _ := by
        simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
        ring
  have h := Summable.tsum_le_tsum hterm (summable_logTrivialZeroTerm hx) hs
  rw [riemannZetaLogTrivialZeroSeries]
  refine h.trans_eq ?_
  rw [tsum_mul_left, Analysis.tsum_shifted_basel_eq]
  ring

/-- Integrate the inverse square on `1 < a ≤ b` by differentiating `-1/x`.
The result is used to bound the integrated trivial-zero correction. -/
theorem inv_sq_integral {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    (∫ t in a..b, t⁻¹ ^ 2) = a⁻¹ - b⁻¹ := by
  have hi : IntervalIntegrable (fun t : ℝ ↦ t⁻¹ ^ 2) MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    intro t ht
    exact
      ((continuousAt_id.inv₀ (ne_of_gt (lt_of_lt_of_le (zero_lt_one.trans ha) ht.1))).pow
          2) |>.continuousWithinAt
  have hd : ∀ t ∈ Set.uIcc a b, HasDerivAt (fun x : ℝ ↦ -x⁻¹) (t⁻¹ ^ 2) t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le (zero_lt_one.trans ha) ht.1)
    have h := (hasDerivAt_inv ht0).neg
    convert h using 1
    simp only [neg_neg, ← inv_pow]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]
  ring

/-- For `1 < a ≤ b`, the integral of the trivial-zero series lies between
zero and the integral of its inverse-square majorant. -/
theorem triv_integral_bound {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    0 ≤ ∫ t in a..b, riemannZetaLogTrivialZeroSeries t ∧
      (∫ t in a..b, riemannZetaLogTrivialZeroSeries t) ≤ (Real.pi ^ 2 / 24) * (a⁻¹ - b⁻¹) := by
  have ht : IntervalIntegrable riemannZetaLogTrivialZeroSeries MeasureTheory.volume a b :=
    (trivial_cont ha).intervalIntegrable_of_Icc hab
  have hi :
    IntervalIntegrable (fun t : ℝ ↦ (Real.pi ^ 2 / 24) * t⁻¹ ^ 2) MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    intro t ht
    exact
      (continuousAt_const.mul
          ((continuousAt_id.inv₀ (ne_of_gt (lt_of_lt_of_le (zero_lt_one.trans ha) ht.1))).pow
            2)) |>.continuousWithinAt
  constructor
  · apply intervalIntegral.integral_nonneg hab
    intro t ht
    exact triv_nonneg (lt_of_lt_of_le ha ht.1)
  · have h :=
      intervalIntegral.integral_mono_on hab ht hi
        (fun t ht ↦ by
          have hh := triv_decay (lt_of_lt_of_le ha ht.1)
          nlinarith only [hh])
    rw [intervalIntegral.integral_const_mul, inv_sq_integral ha hab] at h
    exact h

/-- For `1 < a ≤ b`, the absolute boundary-minus-integral correction of the
trivial-zero series is bounded by `π² / (12a)`. Combine endpoint bounds with
the integral majorant. -/
theorem triv_correction_bound {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    |b * riemannZetaLogTrivialZeroSeries b - a * riemannZetaLogTrivialZeroSeries a -
          ∫ t in a..b, riemannZetaLogTrivialZeroSeries t| ≤
      2 * (Real.pi ^ 2 / 24) * a⁻¹ := by
  have hb : 1 < b := lt_of_lt_of_le ha hab
  have ca : 0 < a := zero_lt_one.trans ha
  have cb : 0 < b := zero_lt_one.trans hb
  have h1 := mul_le_mul_of_nonneg_left (triv_decay ha) ca.le
  have h2 := mul_le_mul_of_nonneg_left (triv_decay hb) cb.le
  have hia : a * a⁻¹ = 1 := mul_inv_cancel₀ ca.ne'
  have hib : b * b⁻¹ = 1 := mul_inv_cancel₀ cb.ne'
  have hea : a * (a⁻¹ ^ 2 * (Real.pi ^ 2 / 24)) = (Real.pi ^ 2 / 24) * a⁻¹ := by
    calc
      _ = (a * a⁻¹) * ((Real.pi ^ 2 / 24) * a⁻¹) := by ring
      _ = _ := by rw [hia, one_mul]
  have heb : b * (b⁻¹ ^ 2 * (Real.pi ^ 2 / 24)) = (Real.pi ^ 2 / 24) * b⁻¹ := by
    calc
      _ = (b * b⁻¹) * ((Real.pi ^ 2 / 24) * b⁻¹) := by ring
      _ = _ := by rw [hib, one_mul]
  have ha' := h1.trans_eq hea
  have hb' := h2.trans_eq heb
  have hapos := mul_nonneg ca.le (triv_nonneg ha)
  have hbpos := mul_nonneg cb.le (triv_nonneg hb)
  have hi := triv_integral_bound ha hab
  apply abs_le.mpr
  constructor <;> linarith only [ha', hb', hapos, hbpos, hi.1, hi.2]

/-- For `1 < a ≤ b`, the absolute integrated trivial-zero correction is at
most one. Combine its inverse-square estimate with a rational upper bound for
π. This supplies the remainder estimate in the integrated explicit formula. -/
theorem triv_correction_le_one {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    |b * riemannZetaLogTrivialZeroSeries b - a * riemannZetaLogTrivialZeroSeries a -
          ∫ t in a..b, riemannZetaLogTrivialZeroSeries t| ≤
      1 := by
  have h := triv_correction_bound ha hab
  have hc : 2 * (Real.pi ^ 2 / 24) ≤ 1 := by
    nlinarith only [Real.pi_lt_d4, Real.pi_pos, sq_nonneg (Real.pi - 31416 / 10000)]
  have ha0 : 0 < a := zero_lt_one.trans ha
  have hi0 : 0 ≤ a⁻¹ := inv_nonneg.mpr ha0.le
  have hi1 : a⁻¹ ≤ 1 := (inv_le_one₀ ha0).2 ha.le
  have hp := mul_le_mul hc hi1 hi0 (by norm_num only : (0 : ℝ) ≤ 1)
  nlinarith only [h, hp]

/-- For `1 < a ≤ b`, the integrated Chebyshev difference is the limit of
its main term and finite nontrivial-zero sums plus a remainder of absolute
value at most one. Use the explicit trivial-zero correction as the remainder. -/
theorem psi1_finite_zero_remainder {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    ∃ r : ℝ,
      |r| ≤ 1 ∧
        Filter.Tendsto
          (fun m : ℕ ↦
            (b ^ 2 - a ^ 2) / 2 - Real.log (2 * Real.pi) * (b - a) +
              (∑
                  ρ ∈
                    (riemannZetaZerosInAnyRectangle (unifiedRectangleLower m)
                          (unifiedTauRectangleUpper 2 m)).filter
                      (fun ρ ↦ ¬ρ.re < 0),
                  -(riemannZetaZeroMultiplicity ρ : ℂ) * ((b : ℂ) ^ (ρ + 1) - (a : ℂ) ^ (ρ + 1)) /
                    (ρ * (ρ + 1))).re +
              r)
          Filter.atTop (nhds (Arithmetic.psiIntegralSum b - Arithmetic.psiIntegralSum a)) := by
  refine
    ⟨-(b * riemannZetaLogTrivialZeroSeries b - a * riemannZetaLogTrivialZeroSeries a -
          ∫ t in a..b, riemannZetaLogTrivialZeroSeries t),
      ?_, ?_⟩
  · rw [abs_neg]
    exact triv_correction_le_one ha hab
  · simpa only [sub_eq_add_neg] using psi1_finite_zero_limit ha hab

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
