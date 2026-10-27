/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.LogWeightedSummationByParts
public import PseudoPrime.Analysis.ExponentialRampVariationBounds
public import PseudoPrime.Analysis.ExponentialRampPairedJumps

/-! # Norm bound for the complete exponential ramp error functional -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- A continuous product with |f|<=K has integral norm at most K times
the absolute density integral. Apply norm domination and monotonicity with
explicit integrability proofs. This bounds each smooth part of the error. -/
private theorem abs_integral_mul_le (f Q : ℝ → ℝ) (hf : Continuous f) (hQ : Continuous Q)
    {K a b : ℝ} (hab : a ≤ b) (hbound : ∀ u ∈ Set.Icc a b, |f u| ≤ K) :
    |∫ u in a..b, f u * Q u| ≤ K * ∫ u in a..b, |Q u| := by
  have hn :=
    intervalIntegral.norm_integral_le_integral_norm (f := fun u ↦ f u * Q u) (μ :=
      MeasureTheory.volume) hab
  simp only [Real.norm_eq_abs] at hn
  have hi :=
    intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hab (f := fun u ↦ |f u * Q u|)
      (g := fun u ↦ K * |Q u|) (((hf.mul hQ).abs).intervalIntegrable a b)
      ((continuous_const.mul hQ.abs).intervalIntegrable a b)
      (fun u hu ↦ by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hbound u hu) (abs_nonneg _))
  rw [intervalIntegral.integral_const_mul] at hi
  exact hn.trans hi

/-- The first variation density is continuous. This supplies its integral norm bound. -/
private theorem ramp_left_cont : Continuous Analysis.exponentialRampVariationLeft :=
  (continuous_id.sub continuous_const).mul (Real.continuous_exp.comp continuous_id.neg)

/-- The middle variation density is continuous. This supplies its integral norm bound. -/
private theorem ramp_middle_cont : Continuous Analysis.exponentialRampVariationMiddle :=
  (Real.continuous_exp.comp continuous_id.neg).mul
    (((continuous_id.sub continuous_const).mul
          ((continuous_const.sub continuous_id).div_const (1 / 200))).add
      ((continuous_const.mul continuous_id).sub continuous_const |>.div_const (1 / 200)))

/-- Four absolute term bounds control |a+b-c+d| by their summed allowances.
Use three triangle inequalities. This preserves both signed jumps. -/
private theorem four_term_abs_le {a b c d A B C D : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) (hc : |c| ≤ C)
    (hd : |d| ≤ D) : |a + b - c + d| ≤ A + B + C + D := by
  have hs := abs_add_le a b
  have ht := abs_sub (a + b) c
  have hu := abs_add_le (a + b - c) d
  linarith only [ha, hb, hc, hd, hs, ht, hu]

/-- A nonnegative jump magnitude transports |f(u)|<=K to |f(u)j|<=Kj.
Use the absolute product identity. This supplies each endpoint allowance. -/
private theorem abs_mul_jump_le {f : ℝ → ℝ} {K u j : ℝ} (hu : |f u| ≤ K) (hj : 0 ≤ j) :
    |f u * j| ≤ K * j := by
  rw [abs_mul, abs_of_nonneg hj]
  exact mul_le_mul_of_nonneg_right hu hj

/-- Restrict the uniform error bound on [0,99/40] to an ordered subinterval.
Apply the continuous product norm bound. This covers the two smooth pieces. -/
private theorem abs_integral_mul_on_cutoff {f Q : ℝ → ℝ} (hf : Continuous f) (hQ : Continuous Q)
    {K a b : ℝ} (hbound : ∀ u ∈ Set.Icc 0 (99 / 40), |f u| ≤ K) (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b ≤ 99 / 40) : |∫ u in a..b, f u * Q u| ≤ K * ∫ u in a..b, |Q u| := by
  exact abs_integral_mul_le f Q hf hQ hab (fun u hu ↦ hbound u ⟨ha.trans hu.1, hu.2.trans hb⟩)

/-- For continuous f bounded by K on the support, the functional norm is at
most K times the actual variation mass. Bound both smooth integrals and both
jump terms. This is the complete finite lower-sum error estimate. -/
theorem exponentialRampVariationFunctional_abs_le_mass {f : ℝ → ℝ} (hf : Continuous f) {K : ℝ}
    (hbound : ∀ u ∈ Set.Icc 0 (99 / 40), |f u| ≤ K) :
    |exponentialRampVariationFunctional f| ≤ K * Analysis.exponentialRampVariationMass := by
  have h1 :=
    abs_integral_mul_on_cutoff hf ramp_left_cont hbound le_rfl
      (by norm_num only : (0 : ℝ) ≤ 247 / 100) (by norm_num only)
  have h2 :=
    abs_integral_mul_on_cutoff hf ramp_middle_cont hbound (by norm_num only : (0 : ℝ) ≤ 247 / 100)
      (by norm_num only) (le_refl (99 / 40))
  have ha :=
    abs_mul_jump_le (hbound (247 / 100) ⟨by norm_num only, by norm_num only⟩) (j :=
      (247 / 100) * Real.exp (-(247 / 100 : ℝ)) / (1 / 200))
      (div_nonneg (mul_nonneg (by norm_num only) (Real.exp_pos _).le) (by norm_num only))
  have hb :=
    abs_mul_jump_le (hbound (99 / 40) ⟨by norm_num only, le_rfl⟩) (j :=
      (99 / 40) * Real.exp (-(99 / 40 : ℝ)) / (1 / 200))
      (div_nonneg (mul_nonneg (by norm_num only) (Real.exp_pos _).le) (by norm_num only))
  apply (four_term_abs_le h1 h2 ha hb).trans_eq
  dsimp only [Analysis.exponentialRampVariationMass]
  ring

/-- For K>=0 and continuous f with |f|<=K on the support, the functional
norm is at most 85K. Use the actual total variation bound.
This supplies the quantitative interface for the sharp RH error. -/
theorem exponentialRampVariationFunctional_abs_le {f : ℝ → ℝ} (hf : Continuous f) {K : ℝ}
    (hK : 0 ≤ K) (hbound : ∀ u ∈ Set.Icc 0 (99 / 40), |f u| ≤ K) :
    |exponentialRampVariationFunctional f| ≤ 85 * K := by
  have hm := mul_le_mul_of_nonneg_left Analysis.variation_mass_le_85 hK
  exact
    (exponentialRampVariationFunctional_abs_le_mass hf hbound).trans (hm.trans_eq (mul_comm K 85))

/-- For a continuous error f bounded by M on the full support and with
short-ramp increment bounded by D, the complete variation functional has
absolute value at most (3/2)M+42D. Pair the signed jumps before estimating
them and use the two small smooth-density masses. This replaces the 85M
estimate when the endpoint increment is controlled. -/
theorem exponentialRampVariationFunctional_abs_le_of_increment {f : ℝ → ℝ} (hf : Continuous f)
    {M D : ℝ} (hb : ∀ u ∈ Set.Icc 0 (99 / 40), |f u| ≤ M) (hd : |f (99 / 40) - f (247 / 100)| ≤ D) :
    |exponentialRampVariationFunctional f| ≤ (3 / 2) * M + 42 * D := by
  have hM := (abs_nonneg (f 0)).trans (hb 0 ⟨le_refl 0, by norm_num only⟩)
  have h1 :=
    abs_integral_mul_on_cutoff hf ramp_left_cont hb le_rfl (by norm_num only : (0 : ℝ) ≤ 247 / 100)
      (by norm_num only)
  have h2 :=
    abs_integral_mul_on_cutoff hf ramp_middle_cont hb (by norm_num only)
      (by norm_num only : (247 / 100 : ℝ) ≤ 99 / 40) (le_refl (99 / 40))
  have hm1 := mul_le_mul_of_nonneg_left Analysis.left_abs_integral_le_one hM
  have hm2 := mul_le_mul_of_nonneg_left Analysis.ramp_middle_abs_integral_le_seven_twentieths hM
  have hj :=
    Analysis.ramp_paired_jumps_abs_le (hb (247 / 100) ⟨by norm_num only, by norm_num only⟩) hd
  let I1 := ∫ u in (0 : ℝ)..(247 / 100), f u * Analysis.exponentialRampVariationLeft u
  let I2 := ∫ u in (247 / 100 : ℝ)..(99 / 40), f u * Analysis.exponentialRampVariationMiddle u
  have ht1 := abs_add_le I1 I2
  have ht2 :=
    abs_add_le (I1 + I2)
      (-(f (247 / 100) * Analysis.rampLeftJump) + f (99 / 40) * Analysis.rampRightJump)
  have he :
    exponentialRampVariationFunctional f =
      I1 + I2 +
        (-(f (247 / 100) * Analysis.rampLeftJump) + f (99 / 40) * Analysis.rampRightJump) := by
    unfold exponentialRampVariationFunctional I1 I2 Analysis.exponentialRampVariationLeft
      Analysis.exponentialRampVariationMiddle Analysis.rampLeftJump Analysis.rampRightJump
    ring
  rw [he]
  nlinarith only [h1, h2, hm1, hm2, hj, ht1, ht2, hM]

end PseudoPrime.AnalyticNumberTheory.Arithmetic
