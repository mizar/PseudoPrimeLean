/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.MellinKernelBounds
public import PseudoPrime.AnalyticNumberTheory.General.MellinWeights

/-! # A compact reciprocal Mellin kernel for finite-scale comparisons -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Input: a complex function, real shifts and a positive argument.
Claim: translation of the kernel multiplies its inverse by the corresponding real-base power.
Proof: split the complex power and pull the constant through the integral.
Role: reuse scalar inversion formulas for shifted rational kernels. -/
theorem inverseMellin_shift (F : ℂ → ℂ) (a c : ℝ) {u : ℝ} (hu : 0 < u) :
    inverseMellin (fun s ↦ F (s + a)) c u = (u : ℂ) ^ (a : ℂ) * inverseMellin F (c + a) u := by
  have he (t : ℝ) :
    F (((c : ℂ) + Complex.I * t) + a) * (u : ℂ) ^ (-((c : ℂ) + Complex.I * t)) =
      (u : ℂ) ^ (a : ℂ) *
        (F (((c + a : ℝ) : ℂ) + Complex.I * t) *
          (u : ℂ) ^ (-(((c + a : ℝ) : ℂ) + Complex.I * t))) := by
    rw [Complex.ofReal_add]
    have hs : (c : ℂ) + Complex.I * t + a = (c : ℂ) + a + Complex.I * t := by ring
    rw [hs]
    have hp : -(↑c + Complex.I * ↑t) = (a : ℂ) + -(↑c + ↑a + Complex.I * ↑t) := by ring
    rw [hp, Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hu.ne')]
    ring
  unfold inverseMellin
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall he),
    MeasureTheory.integral_const_mul]
  ring

/-- Input: a kernel integrable on a vertical line and a positive Mellin argument.
Claim: multiplying by the inverse Mellin power preserves integrability.
Proof: the continuous power has constant norm along that line.
Role: supply the integrability field of new concrete kernels. -/
theorem integrable_inverseMellin_of_line {F : ℂ → ℂ} {c u : ℝ} (hu : 0 < u)
    (hF : MeasureTheory.Integrable (fun t : ℝ ↦ F ((c : ℂ) + Complex.I * t))) :
    MeasureTheory.Integrable
      (fun t : ℝ ↦ F ((c : ℂ) + Complex.I * t) * (u : ℂ) ^ (-((c : ℂ) + Complex.I * t))) := by
  have hp : Continuous (fun t : ℝ ↦ (u : ℂ) ^ (-((c : ℂ) + Complex.I * t))) :=
    (continuous_const.add (continuous_const.mul Complex.continuous_ofReal)).neg.const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hu.ne'))
  exact
    hF.mul_bdd hp.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun _ ↦ (MellinKernel.norm_mellin_power hu).le))

/-- Definition: the rational function 1/((s+1/2)(s+3/2)).
Input: a complex argument, with totalized values at both poles.
Output: a quadratically decaying reciprocal kernel.
Role: obtain a nonnegative inverse supported on the unit interval. -/
noncomputable def reciprocalMellinFunction (s : ℂ) : ℂ :=
  1 / ((s + 1 / 2) * (s + 3 / 2))

/-- Input: a positive vertical coordinate and a positive argument.
Claim: the unshifted reciprocal inverse is the elementary weight max(1-u,0).
Proof: translate the existing Mellin inversion between integral conventions.
Role: provide the scalar base for the shifted compact kernel. -/
theorem inverseMellin_reciprocal_base {c u : ℝ} (hc : 0 < c) (hu : 0 < u) :
    inverseMellin (fun s : ℂ ↦ 1 / (s * (s + 1))) c u =
      AnalyticNumberTheory.General.mellinWeightOne u := by
  rw [← AnalyticNumberTheory.General.mellinInv_mellinWeightOne_eq hc hu]
  unfold inverseMellin mellinInv
  rw [Complex.real_smul]
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards with t
  simp only [smul_eq_mul, mul_comm]

/-- Input: c > -1/2 and u > 0.
Claim: the reciprocal inverse is the real profile sqrt(u) max(1-u,0).
Proof: translate the unshifted inverse and identify the half power with the square root.
Role: prove positivity, compact support and line independence. -/
theorem inverseMellin_reciprocal {c u : ℝ} (hc : -1 / 2 < c) (hu : 0 < u) :
    inverseMellin reciprocalMellinFunction c u = (Real.sqrt u * max (1 - u) 0 : ℝ) := by
  have hf :
    reciprocalMellinFunction = fun s : ℂ ↦ (fun z : ℂ ↦ 1 / (z * (z + 1))) (s + (1 / 2 : ℝ)) := by
    funext s
    dsimp only [reciprocalMellinFunction]
    norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
    congr 2
    ring
  rw [hf, inverseMellin_shift (fun z : ℂ ↦ 1 / (z * (z + 1))) (1 / 2) c hu,
    inverseMellin_reciprocal_base (by linarith only [hc]) hu,
    AnalyticNumberTheory.General.mellinWeightOne_eq_ofReal_max hu]
  rw [← Complex.ofReal_cpow hu.le, ← Real.sqrt_eq_rpow, ← Complex.ofReal_mul]

/-- Input: c > -1/2 and u > 0.
Claim: the reciprocal inverse integrand is absolutely integrable.
Proof: use the shifted reciprocal vertical integral and the bounded Mellin power.
Role: discharge the concrete kernel integrability field. -/
theorem integrable_inverseMellin_reciprocal {c u : ℝ} (hc : -1 / 2 < c) (hu : 0 < u) :
    MeasureTheory.Integrable
      (fun t : ℝ ↦
        reciprocalMellinFunction ((c : ℂ) + Complex.I * t) *
          (u : ℂ) ^ (-((c : ℂ) + Complex.I * t))) := by
  have hcp : 0 < c + 1 / 2 := by linarith only [hc]
  have hi :=
    AnalyticNumberTheory.General.verticalIntegrable_mellinReciprocalKernel hcp.ne'
      (show c + 1 / 2 ≠ -1 by linarith only [hcp])
  apply integrable_inverseMellin_of_line hu
  apply hi.congr
  filter_upwards with t
  dsimp only [reciprocalMellinFunction]
  simp only [Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  ring

/-- Input: a point different from -1/2.
Claim: the first shifted denominator does not vanish.
Proof: additive cancellation.
Role: remove the allowed simple pole when differentiating or regularizing. -/
theorem reciprocal_shift_ne_zero {s : ℂ} (hs : s ≠ -1 / 2) : s + 1 / 2 ≠ 0 := by
  intro he
  apply hs
  calc
    s = -(1 / 2 : ℂ) := eq_neg_of_add_eq_zero_left he
    _ = -1 / 2 := by ring

/-- Input: real part greater than -3/4.
Claim: the second shifted denominator does not vanish.
Proof: a zero would have real part -3/2.
Role: keep the second pole outside the admissible strip. -/
theorem reciprocal_second_shift_ne_zero {s : ℂ} (hs : -3 / 4 < s.re) : s + 3 / 2 ≠ 0 := by
  intro he
  have hr := congrArg Complex.re he
  norm_num only [Complex.add_re, Complex.div_ofNat_re, Complex.re_ofNat, Complex.zero_re] at hr
  linarith only [hr, hs]

/-- Input: real part greater than -3/4 and exclusion of -1/2.
Claim: the reciprocal function is complex differentiable.
Proof: differentiate the product inverse at its two nonzero factors.
Role: prove kernel holomorphy away from the allowed simple pole. -/
theorem differentiableAt_reciprocalMellinFunction {s : ℂ} (hr : -3 / 4 < s.re) (hs : s ≠ -1 / 2) :
    DifferentiableAt ℂ reciprocalMellinFunction s := by
  have hd : DifferentiableAt ℂ (fun z : ℂ ↦ ((z + 1 / 2) * (z + 3 / 2))⁻¹) s :=
    (((differentiableAt_id (𝕜 := ℂ) (x := s)).add_const (1 / 2 : ℂ)).mul
          ((differentiableAt_id (𝕜 := ℂ) (x := s)).add_const (3 / 2 : ℂ))).inv
      (mul_ne_zero (reciprocal_shift_ne_zero hs) (reciprocal_second_shift_ne_zero hr))
  change DifferentiableAt ℂ (fun z : ℂ ↦ 1 / ((z + 1 / 2) * (z + 3 / 2))) s
  simpa only [one_div] using hd

/-- Input: the open strip |Re s| < 3/4 and distance at least eta > 0 from -1/2.
Claim: the kernel norm is at most (3+4/eta)/(1+norm(s)^2).
Proof: small heights use the pole distance; large heights use both imaginary parts.
Role: provide explicit quadratic decay for contour and summability theorems. -/
theorem reciprocalMellinFunction_strip_bound {η : ℝ} (hη : 0 < η) {s : ℂ}
    (hs : -3 / 4 < s.re ∧ s.re < 3 / 4) (hd : η ≤ ‖s + 1 / 2‖) :
    ‖reciprocalMellinFunction s‖ ≤ (3 + 4 / η) / (1 + ‖s‖ ^ 2) := by
  have hA : 0 < ‖s + 1 / 2‖ := hη.trans_le hd
  have hB : (3 / 4 : ℝ) ≤ ‖s + 3 / 2‖ := by
    have hh := Complex.re_le_norm (s + 3 / 2)
    norm_num only [Complex.add_re, Complex.div_ofNat_re, Complex.re_ofNat] at hh
    linarith only [hs.1, hh]
  have hB0 : 0 < ‖s + 3 / 2‖ := lt_of_lt_of_le (by norm_num only) hB
  have hprod0 := mul_pos hA hB0
  have hsr : s.re ^ 2 ≤ 1 := by
    have hm :=
      mul_nonneg (show 0 ≤ s.re + 1 by linarith only [hs.1])
        (show 0 ≤ 1 - s.re by linarith only [hs.2])
    nlinarith only [hm]
  have hsq : ‖s‖ ^ 2 = s.re ^ 2 + s.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  rw [reciprocalMellinFunction, norm_div, norm_one, norm_mul,
    div_le_div_iff₀ hprod0 (show 0 < 1 + ‖s‖ ^ 2 by linarith only [sq_nonneg ‖s‖])]
  by_cases ht : s.im ^ 2 ≤ 1
  · have hp := mul_le_mul hd hB (by norm_num only : (0 : ℝ) ≤ 3 / 4) hA.le
    have hm := mul_le_mul_of_nonneg_left hp (div_nonneg (by norm_num only : (0 : ℝ) ≤ 4) hη.le)
    have he : (4 / η : ℝ) * η = 4 := div_mul_cancel₀ _ hη.ne'
    nlinarith only [hm, he, hsq, hsr, ht, hprod0]
  · have ha := Complex.abs_im_le_norm (s + 1 / 2)
    have hb := Complex.abs_im_le_norm (s + 3 / 2)
    norm_num only [Complex.add_im, Complex.div_ofNat_im, Complex.one_im, Complex.im_ofNat, zero_div,
      add_zero] at ha hb
    have hp := mul_le_mul ha hb (abs_nonneg s.im) hA.le
    rw [← sq, sq_abs] at hp
    have hm := mul_nonneg (div_nonneg (by norm_num only : (0 : ℝ) ≤ 4) hη.le) hprod0.le
    nlinarith only [hp, hm, hsq, hsr, lt_of_not_ge ht]

/-- Input: no parameters.
Definition: the admissible reciprocal kernel with delta=1/8 and the compact inverse profile.
Invariants: holomorphy, regularization, decay, integrability, positivity and line independence.
Role: make the rational kernel available to the existing LLS explicit formula. -/
noncomputable def reciprocalMellinKernel : MellinKernel where
  function := reciprocalMellinFunction
  delta := 1 / 8
  delta_pos := by norm_num only
  region := {s : ℂ | -3 / 4 < s.re ∧ s.re < 3 / 4}
  region_open :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  strip_subset := by
    intro s hs
    exact ⟨by linarith only [hs.1], by linarith only [hs.2]⟩
  holomorphic := by
    intro s hs
    have hz : s ≠ -1 / 2 := by simpa only [Set.mem_singleton_iff] using hs.2
    exact (differentiableAt_reciprocalMellinFunction hs.1.1 hz).differentiableWithinAt
  regularized s := 1 / (s + 3 / 2)
  regularized_holomorphic := by
    intro s hs
    have hd : DifferentiableAt ℂ (fun z : ℂ ↦ (z + 3 / 2)⁻¹) s :=
      ((differentiableAt_id (𝕜 := ℂ) (x := s)).add_const (3 / 2 : ℂ)).inv
        (reciprocal_second_shift_ne_zero hs.1)
    simpa only [one_div] using hd.differentiableWithinAt
  regularized_eq := by
    intro s _ hn
    dsimp only [reciprocalMellinFunction]
    have ha := reciprocal_shift_ne_zero hn
    simp only [one_div] at ha
    simp only [one_div, mul_inv]
    rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul]
  decay := by
    intro η hη
    refine ⟨3 + 4 / η, ?_, ?_⟩
    · exact add_pos_of_pos_of_nonneg (by norm_num only) (div_nonneg (by norm_num only) hη.le)
    · exact fun s hs hd ↦ reciprocalMellinFunction_strip_bound hη hs hd
  mellin_integrable := fun _ _ hc _ hu ↦ integrable_inverseMellin_reciprocal hc hu
  mellin_eq := by
    intro c u hc _ hu
    rw [inverseMellin_reciprocal hc hu, inverseMellin_reciprocal (by norm_num only) hu]
  mellin_nonneg := by
    intro u hu
    rw [inverseMellin_reciprocal (by norm_num only) hu, Complex.ofReal_re]
    exact mul_nonneg (Real.sqrt_nonneg u) (le_max_right _ _)
  mellin_nonzero := by
    refine ⟨1 / 2, by norm_num only, ?_⟩
    rw [inverseMellin_reciprocal (by norm_num only) (by norm_num only), Complex.ofReal_re]
    exact
      (mul_pos (Real.sqrt_pos.mpr (by norm_num only : (0 : ℝ) < 1 / 2))
          ((show (0 : ℝ) < 1 - 1 / 2 by norm_num only).trans_le (le_max_left _ _))).ne'
  mellin_real := by
    intro u hu
    rw [inverseMellin_reciprocal (by norm_num only) hu, Complex.ofReal_im]

/-- Input: a positive argument.
Claim: the admissible kernel transform is sqrt(u) max(1-u,0).
Proof: use the proved scalar inversion on the central line.
Role: identify actual arithmetic summands and their finite support. -/
theorem reciprocalMellinKernel_transform {u : ℝ} (hu : 0 < u) :
    reciprocalMellinKernel.transform u = (Real.sqrt u * max (1 - u) 0 : ℝ) := by
  exact inverseMellin_reciprocal (by norm_num only) hu

/-- Input: the admissible reciprocal kernel.
Claim: its value at the principal endpoint 1/2 is 1/2.
Proof: rational arithmetic.
Role: fix the principal main-term coefficient. -/
theorem reciprocalMellinKernel_endpoint : reciprocalMellinKernel.function (1 / 2) = 1 / 2 := by
  norm_num only [reciprocalMellinKernel, reciprocalMellinFunction]

end PseudoPrime.LLS.PaperStatements
