/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.LogarithmicDecay
public import PseudoPrime.LLS.MellinKernelContour
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaFactorVerticalGrowth
public import PseudoPrime.LLS.MellinKernelArithmeticMellin
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.CompletedVerticalGrowth

/-!
# Vertical Mellin integrability with logarithmic factors

The kernel's quadratic decay dominates a logarithmically growing factor.
The bounded-norm Mellin power preserves absolute integrability on fixed vertical lines.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements.MellinKernel

/-- Every strip line avoiding the kernel pole has a uniform inverse-square pointwise bound.
Its real part fixes a positive distance from the pole; compare the argument norm with
the imaginary parameter. This majorant supports logarithmically weighted integrability. -/
theorem exists_norm_line_le_inverseSquare (K : MellinKernel) {c : ℝ} (hc : -1 / 2 - K.delta < c)
    (hc' : c ≤ 1 / 2 + K.delta) (hne : c ≠ -1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, ‖K.function ((c : ℂ) + Complex.I * t)‖ ≤ C / (1 + t ^ 2) := by
  have hη : 0 < |c + 1 / 2| :=
    abs_pos.mpr
      (by
        intro h
        apply hne
        linarith only [h])
  obtain ⟨C, hC, hb⟩ := K.decay |c + 1 / 2| hη
  refine ⟨C, hC, fun t => ?_⟩
  have hr : ((c : ℂ) + Complex.I * t).re = c := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
  have hi : ((c : ℂ) + Complex.I * t).im = t := by
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, one_mul, zero_mul, zero_add]
  have hs : (c : ℂ) + Complex.I * t ∈ K.region :=
    K.strip_subset
      (by
        rw [Set.mem_ofPred_eq, hr]; exact ⟨hc, hc'⟩)
  have hd : |c + 1 / 2| ≤ ‖(c : ℂ) + Complex.I * t + 1 / 2‖ := by
    have h := Complex.abs_re_le_norm ((c : ℂ) + Complex.I * t + 1 / 2)
    simpa only [Complex.add_re, hr, Complex.div_ofNat_re, Complex.one_re] using h
  have ht := Complex.abs_im_le_norm ((c : ℂ) + Complex.I * t)
  rw [hi] at ht
  have hsq := mul_self_le_mul_self (abs_nonneg t) ht
  rw [← pow_two, ← pow_two, sq_abs] at hsq
  exact
    (hb _ hs hd).trans
      (div_le_div_of_nonneg_left hC.le (by positivity : 0 < 1 + t ^ 2)
        (by linarith only [hsq] : 1 + t ^ 2 ≤ 1 + ‖(c : ℂ) + Complex.I * t‖ ^ 2))

/-- On a strip line avoiding the pole, an almost-everywhere strongly measurable factor
with a logarithmic pointwise bound has integrable product with the kernel.
Apply the inverse-square kernel bound and the real logarithmic decay integral.
This treats logarithmic derivatives without assuming their weighted integrability. -/
theorem integrable_logWeighted_line (K : MellinKernel) {c : ℝ} {F : ℝ → ℂ} {A : ℝ}
    (hc : -1 / 2 - K.delta < c) (hc' : c ≤ 1 / 2 + K.delta) (hne : c ≠ -1 / 2)
    (hF : MeasureTheory.AEStronglyMeasurable F)
    (hb : ∀ t : ℝ, ‖F t‖ ≤ A * (Real.log (4 + |t|) + 1)) :
    MeasureTheory.Integrable (fun t : ℝ => F t * K.function ((c : ℂ) + Complex.I * t)) := by
  obtain ⟨B, _, hK⟩ := exists_norm_line_le_inverseSquare K hc hc' hne
  exact
    Analysis.integrable_mul_of_log_and_inverseSquare hF
      (integrable_line_in_strip K hc hc' hne).aestronglyMeasurable hb hK

/-- On a fixed strip line avoiding the pole, adding the power of a positive real scale
to a logarithmically weighted kernel preserves integrability. The complex power has
constant norm on the vertical line, so bounded multiplication applies.
This gives the vertical integrands used in the completed contour formula. -/
theorem integrable_logWeighted_power_line (K : MellinKernel) {c x : ℝ} {F : ℝ → ℂ} {A : ℝ}
    (hc : -1 / 2 - K.delta < c) (hc' : c ≤ 1 / 2 + K.delta) (hne : c ≠ -1 / 2) (hx : 0 < x)
    (hF : MeasureTheory.AEStronglyMeasurable F)
    (hb : ∀ t : ℝ, ‖F t‖ ≤ A * (Real.log (4 + |t|) + 1)) :
    MeasureTheory.Integrable
      (fun t : ℝ =>
        (F t * K.function ((c : ℂ) + Complex.I * t)) * (x : ℂ) ^ ((c : ℂ) + Complex.I * t)) := by
  have hp : Continuous (fun t : ℝ => (x : ℂ) ^ ((c : ℂ) + Complex.I * t)) :=
    (continuous_const.add (continuous_const.mul Complex.continuous_ofReal)).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))
  apply
    (integrable_logWeighted_line K hc hc' hne hF hb).mul_bdd (c := x ^ c) hp.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro t
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero, le_refl]

open AnalyticNumberTheory.DirichletLFunction in
/-- For any character and a positive scale, the gamma-factor weighted Mellin integrand
is integrable on each right strip line up to real part 3/2. The shifted gamma argument
has positive real part; apply its full-line logarithmic bound and the kernel decay.
This supplies the archimedean part of the completed right vertical integral. -/
theorem integrable_gammaFactor_power_line (K : MellinKernel) {N : ℕ} (χ : DirichletCharacter ℂ N)
    {c x : ℝ} (hc : -1 / 2 < c) (hc' : c ≤ 1 / 2 + K.delta) (hc2 : c ≤ 3 / 2) (hx : 0 < x) :
    MeasureTheory.Integrable
      (fun t : ℝ =>
        (logDeriv χ.gammaFactor (((c : ℂ) + Complex.I * t) + 1 / 2) *
            K.function ((c : ℂ) + Complex.I * t)) *
          (x : ℂ) ^ ((c : ℂ) + Complex.I * t)) := by
  have hσ : 0 < c + 1 / 2 := by linarith only [hc]
  have hσ' : c + 1 / 2 ≤ 2 := by linarith only [hc2]
  obtain ⟨A, _, hb⟩ := exists_norm_logDeriv_gammaFactor_vertical_le_log χ hσ hσ'
  have hl : -1 / 2 - K.delta < c := by linarith only [hc, K.delta_pos]
  have he (t : ℝ) : ((c + 1 / 2 : ℝ) : ℂ) + Complex.I * t = ((c : ℂ) + Complex.I * t) + 1 / 2 := by
    simp only [Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
    ring
  have hi :=
    integrable_logWeighted_power_line K hl hc' (ne_of_gt hc) hx
      (continuous_logDeriv_gammaFactor_vertical χ hσ).aestronglyMeasurable hb
  simpa only [he] using hi

open AnalyticNumberTheory.DirichletLFunction in
/-- For a nonprincipal character and positive scale, the completed negative logarithmic
derivative weighted by the kernel and Mellin power is integrable on each right strip
line with real part between 1/2 and 3/2. Split the completed derivative into the ordinary
Euler-series derivative and gamma-factor derivative, whose integrability is proved.
This removes the right-line integrability assumption in the completed contour limit. -/
theorem integrable_completed_right_line (K : MellinKernel) {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hne : χ ≠ 1) {c x : ℝ} (hc : 1 / 2 < c)
    (hc' : c ≤ 1 / 2 + K.delta) (hc2 : c ≤ 3 / 2) (hx : 0 < x) :
    MeasureTheory.Integrable
      (fun t : ℝ =>
        -logDeriv χ.completedLFunction (((c : ℂ) + Complex.I * t) + 1 / 2) *
          (K.function ((c : ℂ) + Complex.I * t) * (x : ℂ) ^ ((c : ℂ) + Complex.I * t))) := by
  have ha := integrable_arithmeticMellin_logDeriv K χ hx hc hc'
  have hg :=
    integrable_gammaFactor_power_line K χ (lt_trans (by norm_num only : (-1 : ℝ) / 2 < 1 / 2) hc)
      hc' hc2 hx
  apply (ha.sub hg).congr
  apply Filter.Eventually.of_forall
  intro t
  have hr : 1 ≤ (((c : ℂ) + Complex.I * t) + 1 / 2).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero, Complex.div_ofNat_re,
      Complex.one_re]
    linarith only [hc]
  have hp : 0 < (((c : ℂ) + Complex.I * t) + 1 / 2).re := zero_lt_one.trans_le hr
  have he :=
    logDeriv_dirichletLFunction_eq_completed_sub_gammaFactor_of_regular hne
      (completedLFunction_ne_zero_of_one_le_re hne hr) (gammaFactor_ne_zero_of_re_pos χ hp)
      (analyticAt_gammaFactor_of_re_pos χ hp).differentiableAt
  simp only [Pi.sub_apply]
  rw [he]
  ring

open AnalyticNumberTheory.DirichletLFunction in
/-- For a primitive nonprincipal character with nonprincipal inverse and positive scale,
the completed logarithmic Mellin integrand is integrable on each left strip line between
-3/2 and -1/2. The functional equation supplies a logarithmic bound and continuity
of the completed derivative, and kernel decay supplies the integrable majorant.
This removes the left-line integrability assumption in the completed contour limit. -/
theorem integrable_completed_left_line (K : MellinKernel) {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {c x : ℝ}
    (hc : -1 / 2 - K.delta < c) (hc' : c < -1 / 2) (hc2 : -3 / 2 ≤ c) (hx : 0 < x) :
    MeasureTheory.Integrable
      (fun t : ℝ =>
        -logDeriv χ.completedLFunction (((c : ℂ) + Complex.I * t) + 1 / 2) *
          (K.function ((c : ℂ) + Complex.I * t) * (x : ℂ) ^ ((c : ℂ) + Complex.I * t))) := by
  have hσ : c + 1 / 2 < 0 := by linarith only [hc']
  have hσ' : -1 ≤ c + 1 / 2 := by linarith only [hc2]
  obtain ⟨A, _, hb⟩ := exists_norm_completed_vertical_left_le_log hp hne hinv hσ hσ'
  have hu : c ≤ 1 / 2 + K.delta := by linarith only [hc', K.delta_pos]
  have he (t : ℝ) : ((c + 1 / 2 : ℝ) : ℂ) + Complex.I * t = ((c : ℂ) + Complex.I * t) + 1 / 2 := by
    simp only [Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
    ring
  have hi :=
    integrable_logWeighted_power_line K hc hu (ne_of_lt hc') hx
      (continuous_completed_logDeriv_vertical_left hp hne hinv hσ).aestronglyMeasurable hb
  simpa only [he, Pi.neg_def, neg_mul, mul_assoc] using hi.neg

/-- On a kernel strip line avoiding both its own pole and a real pole `p`, the
elementary factor `1/(s-p)` times the kernel and a positive Mellin power is integrable.
The real-part distance gives a uniform denominator bound; the generic logarithmic
majorant then applies. This supplies elementary completion terms in xi contours. -/
theorem integrable_pole_power_line (K : MellinKernel) {c p x : ℝ} (hc : -1 / 2 - K.delta < c)
    (hc' : c ≤ 1 / 2 + K.delta) (hne : c ≠ -1 / 2) (hp : c ≠ p) (hx : 0 < x) :
    MeasureTheory.Integrable
      (fun t : ℝ =>
        ((1 / (((c : ℂ) + Complex.I * t) - (p : ℂ))) * K.function ((c : ℂ) + Complex.I * t)) *
          (x : ℂ) ^ ((c : ℂ) + Complex.I * t)) := by
  have hdist : 0 < |c - p| := abs_pos.mpr (sub_ne_zero.mpr hp)
  have hn (t : ℝ) : ((c : ℂ) + Complex.I * t) - (p : ℂ) ≠ 0 := by
    intro he
    have hr := congrArg Complex.re he
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero,
      Complex.zero_re] at hr
    exact hp (sub_eq_zero.mp hr)
  have hcont : Continuous (fun t : ℝ => 1 / (((c : ℂ) + Complex.I * t) - (p : ℂ))) :=
    continuous_const.div
      ((continuous_const.add (continuous_const.mul Complex.continuous_ofReal)).sub continuous_const)
      hn
  apply
    integrable_logWeighted_power_line K (A := 1 / |c - p|) hc hc' hne hx hcont.aestronglyMeasurable
  intro t
  have hb := Complex.abs_re_le_norm (((c : ℂ) + Complex.I * t) - (p : ℂ))
  simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero] at hb
  have hi := one_div_le_one_div_of_le hdist hb
  have hl : 0 ≤ Real.log (4 + |t|) := Real.log_nonneg (by linarith only [abs_nonneg t])
  rw [one_div, norm_inv, ← one_div]
  exact hi.trans (by nlinarith only [hl, (one_div_pos.mpr hdist).le])

end PseudoPrime.LLS.PaperStatements.MellinKernel
