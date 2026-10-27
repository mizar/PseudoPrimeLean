/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.ZeroGramRows
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.CompletedLogDerivativeNumericalBounds

/-!
# Explicit numerical Dirichlet Gram row allowances

The right line 5/2 supplies logarithmic height dependence and exact leading conductor
coefficient one. The gamma and ordinary Euler estimates require no RH.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- For a real Gamma argument in the vertical strip 2 ≤ Re s ≤ 4, the gamma logarithmic
derivative norm is at most eight plus half log(2+|Im s|). Use the logarithmic digamma
estimate directly, retaining logarithmic rather than linear height dependence. -/
theorem norm_logDeriv_GammaReal_strip_le_log {s : ℂ} (hl : 2 ≤ s.re) (hu : s.re ≤ 4) :
    ‖logDeriv Complex.Gammaℝ s‖ ≤ 8 + Real.log (2 + |s.im|) / 2 := by
  have hp : 0 < s.re := lt_of_lt_of_le (by norm_num only) hl
  have hr : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
    simpa only [Complex.ofReal_zero, add_zero] using
      half_add_ne_neg_nat_of_re_pos hp (a := 0) le_rfl
  have hz : 1 ≤ (s / 2).re := by
    rw [Complex.div_ofNat_re]
    linarith only [hl]
  have hd :=
    Gamma.norm_digamma_le_log_norm_add ((by norm_num only : (1 / 2 : ℝ) ≤ 1).trans hz)
      (hz.trans (Complex.re_le_norm _))
  have hn := Complex.norm_le_abs_re_add_abs_im (s / 2)
  simp only [Complex.div_ofNat_re, Complex.div_ofNat_im, abs_div, abs_of_pos hp,
    abs_of_pos (by norm_num only : (0 : ℝ) < 2)] at hn
  have hn' : ‖s / 2‖ ≤ 2 + |s.im| := by linarith only [hn, hu, abs_nonneg s.im]
  have hl' := Real.log_le_log (lt_of_lt_of_le zero_lt_one (hz.trans (Complex.re_le_norm _))) hn'
  have hlog := Real.log_le_sub_one_of_pos Real.pi_pos
  have hnlog : ‖Complex.log (Real.pi : ℂ)‖ ≤ 3 := by
    rw [← Complex.ofReal_log Real.pi_pos.le, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg (by linarith only [Real.pi_gt_three] : 1 ≤ Real.pi))]
    linarith only [hlog, Real.pi_lt_four]
  rw [logDeriv_Gammaℝ_of_half_ne_neg_nat hr]
  have hnorm := norm_add_le (-(Complex.log (Real.pi : ℂ)) / 2) (Complex.digamma (s / 2) / 2)
  simp only [norm_div, norm_neg, Complex.norm_two] at hnorm
  linarith only [hnorm, hd, hl', hnlog, Real.pi_lt_four, Gamma.digammaLogErrorBound_le_eight]

/-- Both parities at real part 5/2 fit the explicit real Gamma strip. The gamma-factor
logarithmic derivative has the same uniform logarithmic height allowance. -/
theorem norm_logDeriv_gammaFactor_five_halves_le {q : ℕ} (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : s.re = 5 / 2) : ‖logDeriv χ.gammaFactor s‖ ≤ 8 + Real.log (2 + |s.im|) / 2 := by
  have hp : 0 < s.re := by
    rw [hs]; norm_num only
  have hf : (1 : DirichletCharacter ℂ 1).gammaFactor = Complex.Gammaℝ := by
    funext z
    exact principal_modulus_one_even.gammaFactor_def z
  rcases logDeriv_gammaFactor_eq_one_or_one_shift χ hp with he | he
  · rw [he, hf]
    exact
      norm_logDeriv_GammaReal_strip_le_log
        (by
          rw [hs]; norm_num only)
        (by
          rw [hs]; norm_num only)
  · rw [he, hf]
    have hs' : (s + 1).re = 7 / 2 := by
      rw [Complex.add_re, Complex.one_re, hs]; norm_num only
    have h :=
      norm_logDeriv_GammaReal_strip_le_log (s := s + 1)
        (by
          rw [hs']; norm_num only)
        (by
          rw [hs']; norm_num only)
    simpa only [Complex.add_im, Complex.one_im, add_zero] using h

/-- Every nonprincipal character has completed logarithmic derivative norm at 5/2+it
at most ten plus half log(2+|t|). Add the ordinary inverse-gap estimate to the gamma term.
This closes the abstract derivative-budget premise in the exact Gram row bound. -/
theorem norm_logDeriv_completed_five_halves_le {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hne : χ ≠ 1) (t : ℝ) :
    ‖logDeriv χ.completedLFunction (((5 / 2 : ℝ) : ℂ) + t * Complex.I)‖ ≤
      10 + Real.log (2 + |t|) / 2 := by
  let s : ℂ := ((5 / 2 : ℝ) : ℂ) + t * Complex.I
  have hr : s.re = 5 / 2 := by
    simp only [s, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_zero, add_zero]
  have hi : s.im = t := by
    simp only [s, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, zero_mul, mul_one, zero_add, add_zero]
  have hr1 : 1 ≤ s.re := by
    rw [hr]; norm_num only
  have hp : 0 < s.re := zero_lt_one.trans_le hr1
  have he :=
    logDeriv_dirichletLFunction_eq_completed_sub_gammaFactor_of_regular hne
      (completedLFunction_ne_zero_of_one_le_re hne hr1) (gammaFactor_ne_zero_of_re_pos χ hp)
      (analyticAt_gammaFactor_of_re_pos χ hp).differentiableAt
  have ho := norm_logDeriv_le_inv_gap χ (by norm_num only : (1 : ℝ) < 5 / 2) t
  norm_num only at ho
  have hg := norm_logDeriv_gammaFactor_five_halves_le χ hr
  rw [hi] at hg
  have hc :
    logDeriv χ.completedLFunction s = logDeriv χ.LFunction s + logDeriv χ.gammaFactor s := by
    rw [he]
    ring
  change ‖logDeriv χ.completedLFunction s‖ ≤ _
  rw [hc]
  have hn := norm_add_le (logDeriv χ.LFunction s) (logDeriv χ.gammaFactor s)
  linarith only [hn, ho, hg]

/-- The explicit Gram row allowance at modulus q and maximum absolute height H.
The exact conductor coefficient is one; the remaining height dependence is logarithmic. -/
noncomputable def dirichletGramRowBudget (q : ℕ) (H : ℝ) : ℝ :=
  Real.log q + 20 + Real.log (2 + H)

/-- The explicit row allowance is nonnegative for nonnegative height.
This supplies the sign needed when bounding the cut coefficient l2 mass. -/
theorem dirichletGramRowBudget_nonneg (q : ℕ) {H : ℝ} (hH : 0 ≤ H) :
    0 ≤ dirichletGramRowBudget q H := by
  have hl := Real.log_nonneg (by linarith only [hH] : 1 ≤ 2 + H)
  dsimp only [dirichletGramRowBudget]
  linarith only [Real.log_natCast_nonneg q, hl]

/-- Bounding the absolute height by H bounds the actual completed logarithmic derivative
by ten plus half log(2+H). No RH or separate energy hypothesis is used here. -/
theorem completed_logDeriv_re_le_height {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hne : χ ≠ 1) {t H : ℝ} (ht : |t| ≤ H) :
    (logDeriv χ.completedLFunction (((5 / 2 : ℝ) : ℂ) + t * Complex.I)).re ≤
      10 + Real.log (2 + H) / 2 := by
  have hb := norm_logDeriv_completed_five_halves_le hne t
  have hl :=
    Real.log_le_log (by linarith only [abs_nonneg t] : 0 < 2 + |t|)
      (by linarith only [ht] : 2 + |t| ≤ 2 + H)
  have hr := Complex.re_le_norm (logDeriv χ.completedLFunction (((5 / 2 : ℝ) : ℂ) + t * Complex.I))
  linarith only [hb, hl, hr]

/-- The exact finite Dirichlet zero row obeys the explicit modulus and height allowance.
Use the proved completed derivative estimate in the exact Poisson row bound. -/
theorem finite_completed_gram_row_le_numerical {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (S : Finset ℂ) (t : ℝ) :
    ∑ ρ ∈ S,
        (analyticOrderNatAt χ.completedLFunction ρ : ℝ) *
          PseudoPrime.Analysis.ExponentialMeanSquare.gramKernel (t - ρ.im) ≤
      dirichletGramRowBudget q |t| := by
  have hr := finite_completed_gram_row_le hq hRH hp hne hinv S t
  have hb := completed_logDeriv_re_le_height hne (le_rfl : |t| ≤ |t|)
  dsimp only [dirichletGramRowBudget]
  linarith only [hr, hb]

/-- For a fixed primitive nonprincipal individual-RH character and finite height window,
every actual prefix energy is bounded by the explicit row budget times coefficient l2 mass.
The abstract completed-derivative bound is discharged internally. -/
theorem completed_zero_prefix_energy_le_height {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (S : Finset ℂ) (a : ℂ → ℂ) {H : ℝ} (hH : 0 ≤ H)
    (hheight : ∀ ρ ∈ S, |ρ.im| ≤ H) (t : ℝ) :
    PseudoPrime.Analysis.ExponentialMeanSquare.energy
        (PseudoPrime.Analysis.ExponentialMeanSquare.exponentialSum S Complex.im
          (PseudoPrime.Analysis.ExponentialMeanSquare.heightCoefficients Complex.im
            (fun ρ ↦ ((analyticOrderNatAt χ.completedLFunction ρ : ℝ) : ℂ) * a ρ) t)) ≤
      dirichletGramRowBudget q H *
        ∑ ρ ∈ S, (analyticOrderNatAt χ.completedLFunction ρ : ℝ) * ‖a ρ‖ ^ 2 := by
  have hb0 : 0 ≤ 10 + Real.log (2 + H) / 2 := by
    have hl := Real.log_nonneg (by linarith only [hH] : 1 ≤ 2 + H)
    linarith only [hl]
  have h :=
    completed_zero_prefix_energy_le_rows hq hRH hp hne hinv S a hb0
      (fun ρ hρ ↦ completed_logDeriv_re_le_height hne (hheight ρ hρ)) t
  dsimp only [dirichletGramRowBudget]
  convert h using 1
  ring

/-- The explicit fixed-character row budget supplies the actual Abel block point bound.
Only individual RH, primitive nonprincipal data, the finite height window, and coefficients
remain as inputs; all energy and completed-derivative bounds are proved. -/
theorem completed_zero_block_point_le_height {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (S : Finset ℂ) (a : ℂ → ℂ) {H U T : ℝ} (hH : 0 ≤ H)
    (hheight : ∀ ρ ∈ S, |ρ.im| ≤ H) (hU : 0 ≤ U) (hUT : U ≤ T) :
    ‖PseudoPrime.Analysis.ExponentialMeanSquare.exponentialSum S Complex.im
              (PseudoPrime.Analysis.ExponentialMeanSquare.heightCoefficients Complex.im
                (fun ρ ↦ ((analyticOrderNatAt χ.completedLFunction ρ : ℝ) : ℂ) * a ρ) T)
              0 -
            PseudoPrime.Analysis.ExponentialMeanSquare.exponentialSum S Complex.im
              (PseudoPrime.Analysis.ExponentialMeanSquare.heightCoefficients Complex.im
                (fun ρ ↦ ((analyticOrderNatAt χ.completedLFunction ρ : ℝ) : ℂ) * a ρ) U)
              0‖ ^
        2 ≤
      4 * (1 + 2 * T - U) *
        (dirichletGramRowBudget q H *
          ∑ ρ ∈ S, (analyticOrderNatAt χ.completedLFunction ρ : ℝ) * ‖a ρ‖ ^ 2) := by
  apply
    PseudoPrime.Analysis.ExponentialMeanSquare.block_point_le_of_prefix S Complex.im
      (fun ρ ↦ ((analyticOrderNatAt χ.completedLFunction ρ : ℝ) : ℂ) * a ρ) hU hUT
      (mul_nonneg (dirichletGramRowBudget_nonneg q hH)
        (Finset.sum_nonneg (fun ρ hρ ↦ mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))))
  exact fun t ht ↦ completed_zero_prefix_energy_le_height hq hRH hp hne hinv S a hH hheight t

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
