/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.RiemannXi.Growth
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaEntireGrowth
import PseudoPrime.AnalyticNumberTheory.Gamma.GrowthElementary

/-!
# An explicit global xi growth envelope

Combine the Gamma and pole-cancelled zeta bounds on `Re s ≥ 1/2`, then reflect
using the functional equation. The resulting envelope satisfies
`‖riemannXi s‖ ≤ xiOrderOneBound (‖s‖+1)` for every complex `s`.
-/

namespace PseudoPrime.AnalyticNumberTheory.RiemannXi

/-- The real-variable envelope majorizing `‖PseudoPrime.AnalyticNumberTheory.RiemannXi.riemannXi s‖`
in terms of `‖s‖`, for `Re s ≥ 1/2`.
The `1 +` head term makes the bound trivially cover the excluded point `s = 1`
(`PseudoPrime.AnalyticNumberTheory.RiemannXi.riemannXi_eq_gamma_mul_zetaEntire` needs `s ≠ 1`),
where `‖PseudoPrime.AnalyticNumberTheory.RiemannXi.riemannXi 1‖ = 1/2 ≤ 1`. -/
noncomputable def xiOrderOneBound (x : ℝ) : ℝ :=
  1 +
    Real.pi ^ (-(1 : ℝ) / 4) * Real.exp ((x / 2 + 1) * Real.log (x / 2 + 1)) *
      (x + (x + 1) / 2 + x * (x + 1) ^ 2 * RiemannZeta.sawtoothRemainderBound (1 / 2))

theorem xiOrderOneBound_monotoneOn : MonotoneOn xiOrderOneBound (Set.Ici (0 : ℝ)) := by
  intro a ha b hb hab
  simp only [Set.mem_Ici] at ha hb
  unfold xiOrderOneBound
  have hC0 : 0 ≤ RiemannZeta.sawtoothRemainderBound (1 / 2 : ℝ) :=
    RiemannZeta.sawtoothRemainderBound_nonneg _
  have hpolymono :
    a + (a + 1) / 2 + a * (a + 1) ^ 2 * RiemannZeta.sawtoothRemainderBound (1 / 2) ≤
      b + (b + 1) / 2 + b * (b + 1) ^ 2 * RiemannZeta.sawtoothRemainderBound (1 / 2) := by
    gcongr
  have hpolynonneg :
    0 ≤ a + (a + 1) / 2 + a * (a + 1) ^ 2 * RiemannZeta.sawtoothRemainderBound (1 / 2) := by
    have : 0 ≤ a * (a + 1) ^ 2 * RiemannZeta.sawtoothRemainderBound (1 / 2) := by positivity
    linarith
  have hexpmono :
    Real.exp ((a / 2 + 1) * Real.log (a / 2 + 1)) ≤
      Real.exp ((b / 2 + 1) * Real.log (b / 2 + 1)) := by
    apply Real.exp_le_exp.mpr
    exact Gamma.mul_log_mono_of_one_le (by linarith) (by linarith)
  have hexpnonneg : 0 ≤ Real.exp ((a / 2 + 1) * Real.log (a / 2 + 1)) := (Real.exp_pos _).le
  gcongr

theorem one_le_xiOrderOneBound {x : ℝ} (hx : 0 ≤ x) : 1 ≤ xiOrderOneBound x := by
  have h1 : 0 ≤ x + (x + 1) / 2 + x * (x + 1) ^ 2 * RiemannZeta.sawtoothRemainderBound (1 / 2) := by
    have : 0 ≤ x * (x + 1) ^ 2 * RiemannZeta.sawtoothRemainderBound (1 / 2) :=
      mul_nonneg (mul_nonneg hx (by positivity)) (RiemannZeta.sawtoothRemainderBound_nonneg _)
    linarith
  have h2 :
    0 ≤
      Real.pi ^ (-(1 : ℝ) / 4) * Real.exp ((x / 2 + 1) * Real.log (x / 2 + 1)) *
        (x + (x + 1) / 2 + x * (x + 1) ^ 2 * RiemannZeta.sawtoothRemainderBound (1 / 2)) :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg Real.pi_pos.le _) (Real.exp_pos _).le) h1
  unfold xiOrderOneBound
  linarith

/-- **The order-1 growth bound on `Re s ≥ 1/2`.** Assembles the closed form
`PseudoPrime.AnalyticNumberTheory.RiemannXi.riemannXi_eq_gamma_mul_zetaEntire`
with the three factor-wise bounds `norm_cpow_eq_rpow_re_of_pos`
(for `π^{-s/2}`), `PseudoPrime.AnalyticNumberTheory.RiemannZeta.norm_Gamma_le_Gamma_re` +
`PseudoPrime.AnalyticNumberTheory.Gamma.log_Gamma_le_of_one_le` (for `Γ(s/2+1)`), and
`PseudoPrime.AnalyticNumberTheory.RiemannZeta.norm_zetaEntire_le_of_reGt_neg_one` +
`PseudoPrime.AnalyticNumberTheory.RiemannZeta.sawtoothRemainderBound_antitone`
(for `PseudoPrime.AnalyticNumberTheory.RiemannZeta.zetaEntire`). The
point `s = 1` is excluded from the closed form and handled directly via
`PseudoPrime.AnalyticNumberTheory.RiemannXi.riemannXi_one` and
`PseudoPrime.AnalyticNumberTheory.RiemannXi.one_le_xiOrderOneBound`. -/
theorem norm_riemannXi_le_xiOrderOneBound_of_one_half_le_re {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    ‖riemannXi s‖ ≤ xiOrderOneBound ‖s‖ := by
  rcases eq_or_ne s 1 with rfl | hs1
  · rw [riemannXi_one]
    have hval : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by
      rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) from by
          simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat],
        Complex.norm_real]
      rw [Real.norm_of_nonneg (by norm_num only : (0 : ℝ) ≤ 1 / 2)]
    rw [hval]
    exact le_trans (by norm_num only) (one_le_xiOrderOneBound (norm_nonneg _))
  · have hre_half_pos : (0 : ℝ) < s.re / 2 + 1 := by linarith
    have hΓne : Complex.Gamma (s / 2 + 1) ≠ 0 := by
      apply Complex.Gamma_ne_zero_of_re_pos
      simpa only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re] using hre_half_pos
    rw [riemannXi_eq_gamma_mul_zetaEntire hs1 hΓne, norm_mul, norm_mul]
    have hsre_le : s.re ≤ ‖s‖ := (le_abs_self s.re).trans (Complex.abs_re_le_norm s)
    -- Factor 1: `‖π^(-s/2)‖ ≤ π^(-1/4)`.
    have hfac1 : ‖(Real.pi : ℂ) ^ (-s / 2)‖ ≤ Real.pi ^ (-(1 : ℝ) / 4) := by
      have heq : ‖(Real.pi : ℂ) ^ (-s / 2)‖ = Real.pi ^ (-s / 2).re :=
        Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos _
      rw [heq]
      have hre_eq : (-s / 2).re = -(s.re) / 2 := by simp only [Complex.div_ofNat_re, Complex.neg_re]
      rw [hre_eq]
      have hpi1 : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
      exact Real.rpow_le_rpow_of_exponent_le hpi1 (by linarith)
    -- Factor 2: `‖Γ(s/2+1)‖ ≤ exp((‖s‖/2+1)·log(‖s‖/2+1))`.
    have hfac2 :
      ‖Complex.Gamma (s / 2 + 1)‖ ≤ Real.exp ((‖s‖ / 2 + 1) * Real.log (‖s‖ / 2 + 1)) := by
      have hre2_eq : (s / 2 + 1).re = s.re / 2 + 1 := by
        simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re]
      have hstep1 : ‖Complex.Gamma (s / 2 + 1)‖ ≤ Real.Gamma ((s / 2 + 1).re) :=
        RiemannZeta.norm_Gamma_le_Gamma_re
          (by
            rw [hre2_eq]; exact hre_half_pos)
      rw [hre2_eq] at hstep1
      have hlog : Real.log (Real.Gamma (s.re / 2 + 1)) ≤ (s.re / 2 + 1) * Real.log (s.re / 2 + 1) :=
        Gamma.log_Gamma_le_of_one_le (by linarith)
      have hGammapos : 0 < Real.Gamma (s.re / 2 + 1) := Real.Gamma_pos_of_pos (by linarith)
      have hstep2 :
        Real.Gamma (s.re / 2 + 1) ≤ Real.exp ((s.re / 2 + 1) * Real.log (s.re / 2 + 1)) := by
        calc
          Real.Gamma (s.re / 2 + 1) = Real.exp (Real.log (Real.Gamma (s.re / 2 + 1))) :=
            (Real.exp_log hGammapos).symm
          _ ≤ Real.exp ((s.re / 2 + 1) * Real.log (s.re / 2 + 1)) := Real.exp_le_exp.mpr hlog
      have hstep3 :
        Real.exp ((s.re / 2 + 1) * Real.log (s.re / 2 + 1)) ≤
          Real.exp ((‖s‖ / 2 + 1) * Real.log (‖s‖ / 2 + 1)) := by
        apply Real.exp_le_exp.mpr
        exact Gamma.mul_log_mono_of_one_le (by linarith) (by linarith)
      exact hstep1.trans (hstep2.trans hstep3)
    -- Factor 3: `‖RiemannZeta.zetaEntire s‖` is polynomially bounded.
    have hfac3 :
      ‖RiemannZeta.zetaEntire s‖ ≤
        ‖s‖ + (‖s‖ + 1) / 2 + ‖s‖ * (‖s‖ + 1) ^ 2 * RiemannZeta.sawtoothRemainderBound (1 / 2) := by
      have hz := RiemannZeta.norm_zetaEntire_le_of_reGt_neg_one (s := s) (by linarith)
      have hsaw_le :
        RiemannZeta.sawtoothRemainderBound s.re ≤ RiemannZeta.sawtoothRemainderBound (1 / 2) :=
        RiemannZeta.sawtoothRemainderBound_antitone (by norm_num only) hs
      calc
        ‖RiemannZeta.zetaEntire s‖ ≤
            ‖s‖ + (‖s‖ + 1) / 2 + ‖s‖ * (‖s‖ + 1) ^ 2 * RiemannZeta.sawtoothRemainderBound s.re :=
          hz
        _ ≤
            ‖s‖ + (‖s‖ + 1) / 2 +
              ‖s‖ * (‖s‖ + 1) ^ 2 * RiemannZeta.sawtoothRemainderBound (1 / 2) :=
          by gcongr
    have hcombine :
      ‖(Real.pi : ℂ) ^ (-s / 2)‖ * ‖Complex.Gamma (s / 2 + 1)‖ * ‖RiemannZeta.zetaEntire s‖ ≤
        Real.pi ^ (-(1 : ℝ) / 4) * Real.exp ((‖s‖ / 2 + 1) * Real.log (‖s‖ / 2 + 1)) *
          (‖s‖ + (‖s‖ + 1) / 2 +
            ‖s‖ * (‖s‖ + 1) ^ 2 * RiemannZeta.sawtoothRemainderBound (1 / 2)) := by
      gcongr
    unfold xiOrderOneBound
    linarith [hcombine]

/-- The global xi norm bound follows from the right-half-plane estimate,
monotonicity of the envelope, and reflection `s ↦ 1-s`.
It supplies the growth input for finite-radius canonical-decomposition estimates. -/
theorem norm_riemannXi_le_xiOrderOneBound (s : ℂ) : ‖riemannXi s‖ ≤ xiOrderOneBound (‖s‖ + 1) :=
  norm_riemannXi_le_of_forall_one_half_le_re xiOrderOneBound_monotoneOn
    (fun _ ht => norm_riemannXi_le_xiOrderOneBound_of_one_half_le_re ht) s

/-- The order-one envelope bounds xi uniformly on a closed ball of nonnegative
radius. This supplies the boundary growth input for canonical factor estimates. -/
theorem norm_riemannXi_le_xiOrderOneBound_on_closedBall {R : ℝ} (hR : 0 ≤ R) {s : ℂ}
    (hs : s ∈ Metric.closedBall (0 : ℂ) R) : ‖riemannXi s‖ ≤ xiOrderOneBound (R + 1) := by
  have hnorm := norm_riemannXi_le_xiOrderOneBound s
  rw [Metric.mem_closedBall, dist_zero_right] at hs
  apply hnorm.trans
  apply xiOrderOneBound_monotoneOn
  · change 0 ≤ ‖s‖ + 1
    positivity
  · change 0 ≤ R + 1
    linarith
  · linarith

end PseudoPrime.AnalyticNumberTheory.RiemannXi
