/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LogZeroAntiderivative
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ExponentialLogWeightedSummation

/-! # Splitting the integrated explicit formula

Separate pole, nontrivial-zero and trivial-zero contributions.
-/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- For `1 ≤ a`, the logarithmic trivial-zero series is continuous on
`[a, b]`. Its value at one provides a summable majorant for all terms. -/
theorem trivial_cont_closed {a b : ℝ} (ha : 1 ≤ a) :
    ContinuousOn riemannZetaLogTrivialZeroSeries (Set.Icc a b) := by
  unfold riemannZetaLogTrivialZeroSeries
  apply continuousOn_tsum (u := fun k : ℕ ↦ (1 / 4 : ℝ) * (1 / ((k : ℝ) + 1) ^ 2))
  · intro k x hx
    have hx0 : x ≠ 0 := ne_of_gt (lt_of_lt_of_le (zero_lt_one.trans_le ha) hx.1)
    exact (((continuousAt_id.inv₀ hx0).pow _).div_const _).continuousWithinAt
  · have h := hasSum_zeta_two.summable.comp_injective Nat.succ_injective
    change Summable (fun k : ℕ ↦ (1 : ℝ) / ((k + 1 : ℕ) : ℝ) ^ 2) at h
    have hs : Summable (fun k : ℕ ↦ (1 : ℝ) / ((k : ℝ) + 1) ^ 2) := by
      simpa only [Nat.cast_add, Nat.cast_one] using h
    exact hs.mul_left (1 / 4)
  · intro k x hx
    have ha0 : 0 < a := zero_lt_one.trans_le ha
    have hi0 : 0 ≤ x⁻¹ := inv_nonneg.mpr (le_trans ha0.le hx.1)
    have hi : x⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (ha.trans hx.1)
    have hp := pow_le_pow_left₀ hi0 hi (2 * (k + 1))
    have hd : 0 ≤ 4 * ((k : ℝ) + 1) ^ 2 := mul_nonneg (by norm_num only) (sq_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (pow_nonneg hi0 _) hd)]
    simpa only [one_pow, one_div, mul_inv_rev, mul_comm] using div_le_div_of_nonneg_right hp hd

/-- For a left endpoint strictly above one, the logarithmic trivial-zero
series is continuous on the closed interval by the estimate valid at one. -/
theorem trivial_cont {a b : ℝ} (ha : 1 < a) :
    ContinuousOn riemannZetaLogTrivialZeroSeries (Set.Icc a b) := by exact trivial_cont_closed ha.le

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

/-- At the lower endpoint one, the exact logarithmic formula follows by
right continuity of the weighted sum and both zero series. -/
theorem log_weighted_exact_one :
    Arithmetic.logWeightedMangoldtSum 1 =
      -RiemannXi.qMinusOneRiemannZetaSecondLogDerivAtZero.re - Real.log (2 * Real.pi) * Real.log 1 +
          1 +
          (∑' ρ : ℂ, nontrivialLogZeroTerm 1 ρ).re -
        riemannZetaLogTrivialZeroSeries 1 := by
  have h₁ : (1 : ℝ) ∈ Set.Icc 1 2 := ⟨le_rfl, by norm_num only⟩
  have hL :=
    (Arithmetic.continuousOn_logWeightedMangoldtSum_scaled (x := 1) zero_lt_one 2).mono
      (Set.Icc_subset_Icc_left zero_le_one)
  simp only [one_mul] at hL
  have hlog : ContinuousOn Real.log (Set.Icc (1 : ℝ) 2) := fun t ht ↦
    (Real.continuousAt_log (ne_of_gt (zero_lt_one.trans_le ht.1))).continuousWithinAt
  have hz :=
    Complex.continuous_re.comp_continuousOn (zero_sum_continuous (b := 2) (le_refl (1 : ℝ)))
  have hc :
    ContinuousOn (fun _ : ℝ ↦ -RiemannXi.qMinusOneRiemannZetaSecondLogDerivAtZero.re)
      (Set.Icc (1 : ℝ) 2) :=
    continuousOn_const
  have hR :=
    ((((hc.sub (hlog.const_mul (Real.log (2 * Real.pi)))).add continuousOn_id).add hz).sub
      (trivial_cont_closed (b := 2) (le_refl (1 : ℝ))))
  have hs : Set.Ioc (1 : ℝ) 2 ⊆ Set.Icc 1 2 := fun _ ht ↦ ⟨ht.1.le, ht.2⟩
  have : (nhdsWithin (1 : ℝ) (Set.Ioc 1 2)).NeBot := by
    apply mem_closure_iff_nhdsWithin_neBot.mp
    rw [closure_Ioc (by norm_num only : (1 : ℝ) ≠ 2)]
    exact h₁
  have he := ((hL 1 h₁).mono hs).tendsto
  apply tendsto_nhds_unique he
  apply ((hR 1 h₁).mono hs).tendsto.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (log_weighted_exact ht.1).symm

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
