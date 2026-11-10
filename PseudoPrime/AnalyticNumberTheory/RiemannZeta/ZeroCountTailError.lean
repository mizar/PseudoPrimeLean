/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountTail
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountIntegral
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountErrorNumerics

/-! # Zero-count errors in the inverse-square tail -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Integrate a logarithmic zero-count main term with error `2 log t`
against the inverse-cube Abel kernel on positive ordered endpoints. -/
theorem count_tail_main_integral {a b k c d : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, (k * t * (Real.log t - c - 1) + d + 2 * Real.log t) * (2 * t⁻¹ ^ 3)) =
      (-2 * k * (Real.log b - c) / b - (d + 2 * Real.log b + 1) / b ^ 2) -
        (-2 * k * (Real.log a - c) / a - (d + 2 * Real.log a + 1) / a ^ 2) := by
  have hi :
    IntervalIntegrable
      (fun t : ℝ ↦ (k * t * (Real.log t - c - 1) + d + 2 * Real.log t) * (2 * t⁻¹ ^ 3))
      MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le ha ht.1)
    have hl := Real.continuousAt_log ht0
    exact
      (((((continuousAt_const.mul continuousAt_id).mul
                      ((hl.sub continuousAt_const).sub continuousAt_const)).add
                  continuousAt_const).add
              (continuousAt_const.mul hl)).mul
          (continuousAt_const.mul ((continuousAt_id.inv₀ ht0).pow 3))).continuousWithinAt
  have hd :
    ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun x : ℝ ↦ -2 * k * (Real.log x - c) / x - (d + 2 * Real.log x + 1) / x ^ 2)
        ((k * t * (Real.log t - c - 1) + d + 2 * Real.log t) * (2 * t⁻¹ ^ 3)) t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le ha ht.1)
    have hl := Real.hasDerivAt_log ht0
    have h1 := (((hl.sub_const c).const_mul (-2 * k)).div (hasDerivAt_id t) ht0)
    have h2 :=
      (((hl.const_mul 2).const_add d).add_const 1).div ((hasDerivAt_id t).pow 2) (pow_ne_zero 2 ht0)
    have h := h1.sub h2
    convert h using 1
    · funext x
      rfl
    · simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one]
      field_simp
      ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]

/-- On a positive bounded interval, the zero count times the inverse-cube
kernel is interval integrable. Multiply the integrable count by a continuous
kernel. -/
theorem zeroCount_invCube_integrable {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t ↦ zeroCount t * (2 * t⁻¹ ^ 3)) MeasureTheory.volume a b := by
  have hp := zeroCount_integrable ha.le hab
  have hc : ContinuousOn (fun t : ℝ ↦ 2 * t⁻¹ ^ 3) (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]
    intro t ht
    exact
      (continuousAt_const.mul
          ((continuousAt_id.inv₀ (ne_of_gt (lt_of_lt_of_le ha ht.1))).pow 3)).continuousWithinAt
  exact hp.mul_continuousOn hc

/-- A continuous approximation `M` and continuous error bound `E` for the
two-sided zero count give an upper bound for each finite inverse-square tail.
Use the lower count bound at the entrance, the upper bound at the exit, and
integrate the upper bound against the nonnegative inverse-cube kernel. -/
theorem finite_tail_of_count_error {a b : ℝ} {M E : ℝ → ℝ} (ha : 1 < a) (hab : a ≤ b)
    (hM : ContinuousOn M (Set.Icc a b)) (hE : ContinuousOn E (Set.Icc a b))
    (hQ : ∀ t ∈ Set.Icc a b, |zeroCount t - M t| ≤ E t) :
    (∑ ρ ∈ (zerosUpTo b).filter (fun ρ ↦ a < |ρ.im|),
        (riemannZetaZeroMultiplicity ρ : ℝ) / |ρ.im| ^ 2) ≤
      (M b + E b) / b ^ 2 - (M a - E a) / a ^ 2 + ∫ t in a..b, (M t + E t) * (2 * t⁻¹ ^ 3) := by
  have ha0 : 0 < a := zero_lt_one.trans ha
  have hc : ContinuousOn (fun t : ℝ ↦ 2 * t⁻¹ ^ 3) (Set.Icc a b) := by
    intro t ht
    exact
      (continuousAt_const.mul
          ((continuousAt_id.inv₀ (ne_of_gt (lt_of_lt_of_le ha0 ht.1))).pow 3)).continuousWithinAt
  have hm : IntervalIntegrable (fun t ↦ (M t + E t) * (2 * t⁻¹ ^ 3)) MeasureTheory.volume a b :=
    ((hM.add hE).mul hc).intervalIntegrable_of_Icc hab
  have hint :=
    intervalIntegral.integral_mono_on hab (zeroCount_invCube_integrable ha0 hab) hm
      (fun t ht ↦ by
        have h := (abs_le.mp (hQ t ht)).2
        have hk : 0 ≤ 2 * t⁻¹ ^ 3 :=
          mul_nonneg (by norm_num only) (pow_nonneg (inv_nonneg.mpr (lt_of_lt_of_le ha0 ht.1).le) 3)
        exact mul_le_mul_of_nonneg_right (show zeroCount t ≤ M t + E t by linarith only [h]) hk)
  have hQa := abs_le.mp (hQ a ⟨le_rfl, hab⟩)
  have hQb := abs_le.mp (hQ b ⟨hab, le_rfl⟩)
  have hda :=
    div_le_div_of_nonneg_right (show M a - E a ≤ zeroCount a by linarith only [hQa.1]) (sq_nonneg a)
  have hdb :=
    div_le_div_of_nonneg_right (show zeroCount b ≤ M b + E b by linarith only [hQb.2]) (sq_nonneg b)
  rw [finite_tail_abel ha hab]
  linarith only [hint, hda, hdb]

/-- Under RH, a continuous approximation and error bound for the zero count
bound the full ordinate tail by the limit of their finite Abel expressions.
The zero-count error and existence of the stated limit are hypotheses. -/
theorem ordinateTail_of_count_error (hRH : RiemannHypothesis) {a C : ℝ} {M E : ℝ → ℝ} (ha : 1 < a)
    (hM : ContinuousOn M (Set.Ici a)) (hE : ContinuousOn E (Set.Ici a))
    (hQ : ∀ t ∈ Set.Ici a, |zeroCount t - M t| ≤ E t)
    (hlim :
      Filter.Tendsto
        (fun b : ℝ ↦
          (M b + E b) / b ^ 2 - (M a - E a) / a ^ 2 + ∫ t in a..b, (M t + E t) * (2 * t⁻¹ ^ 3))
        Filter.atTop (nhds C)) :
    ordinateTail a ≤ C := by
  apply le_of_tendsto_of_tendsto (ordinateTail_limit hRH a) hlim
  filter_upwards [Filter.eventually_ge_atTop a] with b hb
  apply finite_tail_of_count_error ha hb
  · exact hM.mono (fun t ht ↦ ht.1)
  · exact hE.mono (fun t ht ↦ ht.1)
  · exact fun t ht ↦ hQ t ht.1

/-- A `2 log t` error for a logarithmic zero-count approximation bounds the
finite inverse-square tail by an explicit expression at both endpoints. -/
theorem finite_tail_of_log_error {a b k c d : ℝ} (ha : 1 < a) (hab : a ≤ b)
    (hM : ContinuousOn (fun t ↦ k * t * (Real.log t - c - 1) + d) (Set.Icc a b))
    (hQ : ∀ t ∈ Set.Icc a b, |zeroCount t - (k * t * (Real.log t - c - 1) + d)| ≤ 2 * Real.log t) :
    (∑ ρ ∈ (zerosUpTo b).filter (fun ρ ↦ a < |ρ.im|),
        (riemannZetaZeroMultiplicity ρ : ℝ) / |ρ.im| ^ 2) ≤
      k * (Real.log a - c + 1) / a + (4 * Real.log a + 1) / a ^ 2 - k * (Real.log b - c + 1) / b -
        1 / b ^ 2 := by
  have ha0 : 0 < a := zero_lt_one.trans ha
  have hE : ContinuousOn (fun t : ℝ ↦ 2 * Real.log t) (Set.Icc a b) := by
    intro t ht
    exact
      (continuousAt_const.mul
          (Real.continuousAt_log (ne_of_gt (lt_of_lt_of_le ha0 ht.1)))).continuousWithinAt
  have h := finite_tail_of_count_error ha hab hM hE hQ
  rw [count_tail_main_integral ha0 hab] at h
  have heq :
    (k * b * (Real.log b - c - 1) + d + 2 * Real.log b) / b ^ 2 -
          (k * a * (Real.log a - c - 1) + d - 2 * Real.log a) / a ^ 2 +
        ((-2 * k * (Real.log b - c) / b - (d + 2 * Real.log b + 1) / b ^ 2) -
          (-2 * k * (Real.log a - c) / a - (d + 2 * Real.log a + 1) / a ^ 2)) =
      k * (Real.log a - c + 1) / a + (4 * Real.log a + 1) / a ^ 2 - k * (Real.log b - c + 1) / b -
        1 / b ^ 2 := by
    have ha1 : a ≠ 0 := ne_of_gt ha0
    have hb1 : b ≠ 0 := ne_of_gt (lt_of_lt_of_le ha0 hab)
    field_simp
    ring
  rw [heq] at h
  exact h

/-- Under RH and a `2 log t` zero-count error bound, the infinite ordinate
tail is bounded by the explicit lower-endpoint expression. The count error is
an assumption; the proof passes the finite estimate to the limit. -/
theorem ordinateTail_of_log_error (hRH : RiemannHypothesis) {a k c d : ℝ} (ha : 1 < a) (hk : 0 ≤ k)
    (hc : c ≤ Real.log a)
    (hQ : ∀ t ∈ Set.Ici a, |zeroCount t - (k * t * (Real.log t - c - 1) + d)| ≤ 2 * Real.log t) :
    ordinateTail a ≤ k * (Real.log a - c + 1) / a + (4 * Real.log a + 1) / a ^ 2 := by
  apply ordinateTail_le_of_eventually hRH
  filter_upwards [Filter.eventually_ge_atTop a] with b hb
  have ha0 : 0 < a := zero_lt_one.trans ha
  have hM : ContinuousOn (fun t ↦ k * t * (Real.log t - c - 1) + d) (Set.Icc a b) := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le ha0 ht.1)
    exact
      (((continuousAt_const.mul continuousAt_id).mul
              (((Real.continuousAt_log ht0).sub continuousAt_const).sub continuousAt_const)).add
          continuousAt_const).continuousWithinAt
  have h := finite_tail_of_log_error ha hb hM (fun t ht ↦ hQ t ht.1)
  have hl := Real.log_le_log ha0 hb
  have hlog : 0 ≤ Real.log b - c + 1 := by linarith only [hc, hl]
  have hb0 : 0 ≤ b := (lt_of_lt_of_le ha0 hb).le
  have hterm : 0 ≤ k * (Real.log b - c + 1) / b := div_nonneg (mul_nonneg hk hlog) hb0
  have hterm2 : 0 ≤ (1 : ℝ) / b ^ 2 := div_nonneg (by norm_num only) (sq_nonneg b)
  linarith only [h, hterm, hterm2]

/-- Under RH and the stated two-sided zero-count error bound, the ordinate
tail is at most `log a / (πa)` for `a ≥ 1000`. The numerical absorption uses
the explicit preliminary estimate; the count error remains a hypothesis. -/
theorem ordinateTail_of_count (hRH : RiemannHypothesis) {a : ℝ} (ha : 1000 ≤ a)
    (hQ :
      ∀ t ∈ Set.Ici a,
        |zeroCount t - ((1 / Real.pi) * t * (Real.log t - Real.log (2 * Real.pi) - 1) + 7 / 4)| ≤
          2 * Real.log t) :
    ordinateTail a ≤ Real.log a / (Real.pi * a) := by
  have ha0 : 0 < a := by linarith only [ha]
  have hpi : 0 < 2 * Real.pi := mul_pos (by norm_num only) Real.pi_pos
  have hc : Real.log (2 * Real.pi) ≤ Real.log a := by
    apply Real.log_le_log hpi
    linarith only [Real.pi_lt_four, ha]
  have hk : 0 ≤ (1 / Real.pi : ℝ) := div_nonneg (by norm_num only) Real.pi_pos.le
  have h :=
    ordinateTail_of_log_error hRH (k := 1 / Real.pi) (c := Real.log (2 * Real.pi)) (d := 7 / 4)
      (by linarith only [ha]) hk hc hQ
  apply zero_tail_of_preliminary ha
  rw [Real.log_div ha0.ne' hpi.ne']
  convert h using 1
  ring

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
