/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LogZeroAntiderivative

/-! # Splitting the integrated explicit formula

Separate pole, nontrivial-zero and trivial-zero contributions.
-/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- For `1 < a`, the logarithmic trivial-zero series is continuous on
`[a, b]`. Its value at `a` provides a summable majorant for all terms. -/
theorem trivial_cont {a b : ℝ} (ha : 1 < a) :
    ContinuousOn riemannZetaLogTrivialZeroSeries (Set.Icc a b) := by
  unfold riemannZetaLogTrivialZeroSeries
  apply continuousOn_tsum (u := fun k : ℕ ↦ a⁻¹ ^ (2 * (k + 1)) / (4 * ((k : ℝ) + 1) ^ 2))
  · intro k x hx
    have hx0 : x ≠ 0 := ne_of_gt (lt_of_lt_of_le (zero_lt_one.trans ha) hx.1)
    exact (((continuousAt_id.inv₀ hx0).pow _).div_const _).continuousWithinAt
  · exact summable_logTrivialZeroTerm ha
  · intro k x hx
    have ha0 : 0 < a := zero_lt_one.trans ha
    have hi0 : 0 ≤ x⁻¹ := inv_nonneg.mpr (le_trans ha0.le hx.1)
    have hi : x⁻¹ ≤ a⁻¹ := inv_le_inv₀ (lt_of_lt_of_le ha0 hx.1) ha0 |>.2 hx.1
    have hp := pow_le_pow_left₀ hi0 hi (2 * (k + 1))
    have hd : 0 ≤ 4 * ((k : ℝ) + 1) ^ 2 := mul_nonneg (by norm_num only) (sq_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (pow_nonneg hi0 _) hd)]
    exact div_le_div_of_nonneg_right hp hd

/-- For `1 < a ≤ b`, split the integral of the exact logarithmic formula
into its pole, nontrivial-zero and trivial-zero contributions. Continuity
and the uniform zero bound justify the three interval integrals. -/
theorem log_integral_split {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    (∫ t in a..b, logExplicit t) =
      (∫ t in a..b,
            (-RiemannXi.qMinusOneRiemannZetaSecondLogDerivAtZero.re -
                Real.log (2 * Real.pi) * Real.log t +
              t)) +
          (∫ t in a..b, ∑' ρ : ℂ, nontrivialLogZeroTerm t ρ).re -
        ∫ t in a..b, riemannZetaLogTrivialZeroSeries t := by
  have hc : ContinuousOn Real.log (Set.Icc a b) := by
    apply Real.continuousOn_log.mono
    intro t ht
    exact ne_of_gt (lt_of_lt_of_le (zero_lt_one.trans ha) ht.1)
  have hm :
    IntervalIntegrable
      (fun t : ℝ ↦
        -RiemannXi.qMinusOneRiemannZetaSecondLogDerivAtZero.re -
            Real.log (2 * Real.pi) * Real.log t +
          t)
      MeasureTheory.volume a b :=
    ((continuousOn_const.sub (continuousOn_const.mul hc)).add
        continuousOn_id) |>.intervalIntegrable_of_Icc
      hab
  have hz := zero_sum_integrable ha.le hab
  have hzr :
    IntervalIntegrable (fun t ↦ (∑' ρ : ℂ, nontrivialLogZeroTerm t ρ).re) MeasureTheory.volume a
      b :=
    (Complex.continuous_re.continuousOn.comp (zero_sum_continuous ha.le)
          (fun _ _ ↦ Set.mem_univ _)).intervalIntegrable_of_Icc
      hab
  have ht : IntervalIntegrable riemannZetaLogTrivialZeroSeries MeasureTheory.volume a b :=
    (trivial_cont ha).intervalIntegrable_of_Icc hab
  simp only [logExplicit_eq]
  rw [intervalIntegral.integral_sub (hm.add hzr) ht, intervalIntegral.integral_add hm hzr]
  have hr := Complex.reCLM.intervalIntegral_comp_comm hz
  change
    (∫ t in a..b, (∑' ρ : ℂ, nontrivialLogZeroTerm t ρ).re) =
      (∫ t in a..b, ∑' ρ : ℂ, nontrivialLogZeroTerm t ρ).re at hr
  rw [hr]

/-- For `1 < a ≤ b`, split the integrated Chebyshev difference into pole,
nontrivial-zero and trivial-zero parts. The zero contribution retains its
boundary terms and its integral for the zero-ledger limit. -/
theorem psi1_diff_split {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    Arithmetic.psiIntegralSum b - Arithmetic.psiIntegralSum a =
      (b *
              (-RiemannXi.qMinusOneRiemannZetaSecondLogDerivAtZero.re -
                  Real.log (2 * Real.pi) * Real.log b +
                b) -
            a *
              (-RiemannXi.qMinusOneRiemannZetaSecondLogDerivAtZero.re -
                  Real.log (2 * Real.pi) * Real.log a +
                a) -
            ∫ t in a..b,
              (-RiemannXi.qMinusOneRiemannZetaSecondLogDerivAtZero.re -
                  Real.log (2 * Real.pi) * Real.log t +
                t)) +
          ((b : ℂ) * (∑' ρ : ℂ, nontrivialLogZeroTerm b ρ) -
              (a : ℂ) * (∑' ρ : ℂ, nontrivialLogZeroTerm a ρ) -
              ∫ t in a..b, ∑' ρ : ℂ, nontrivialLogZeroTerm t ρ).re -
        (b * riemannZetaLogTrivialZeroSeries b - a * riemannZetaLogTrivialZeroSeries a -
          ∫ t in a..b, riemannZetaLogTrivialZeroSeries t) := by
  rw [psi1_diff_logExplicit ha hab, log_integral_split ha hab]
  simp only [logExplicit_eq]
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero]
  ring

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
