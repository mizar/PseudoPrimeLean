/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.SharpGaussianPrincipalBounds

/-! # Gaussian moment cell and finite-grid bounds -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- The Gaussian normalization factor is at most 113/200.
The rational lower bound for pi gives the positive square-root comparison. -/
theorem inv_sqrt_pi_le_113_div_200 : (Real.sqrt Real.pi)⁻¹ ≤ (113 / 200 : ℝ) := by
  have hp : (157 / 50 : ℝ) ≤ Real.pi := by linarith only [Real.pi_gt_d20]
  have hs := Real.sq_sqrt Real.pi_pos.le
  have hs0 := Real.sqrt_pos.mpr Real.pi_pos
  have hb : (200 / 113 : ℝ) ≤ Real.sqrt Real.pi := by nlinarith only [hp, hs, hs0]
  rw [← one_div, div_le_iff₀ hs0]
  nlinarith only [hb]

/-- On a real cell, lower bounds for the square and the inner exponential,
and an upper bound for the resulting exponential, bound the Gaussian density.
This transfers rational cell certificates to the actual smoothing integrand. -/
theorem gaussian_density_cell_upper {a b v k l s e U : ℝ} (hav : a ≤ v) (hvb : v ≤ b) (hk : 0 ≤ k)
    (hl : 0 ≤ l) (hs : s ≤ v ^ 2) (he : e ≤ Real.exp (-b))
    (hU : Real.exp (-s - k * a - l * e) ≤ U) :
    Analysis.normalizedGaussianWeight v * Real.exp (-k * v) * Real.exp (-l * Real.exp (-v)) ≤
      (113 / 200 : ℝ) * U := by
  have he' : e ≤ Real.exp (-v) := he.trans (Real.exp_le_exp.mpr (neg_le_neg hvb))
  have hk' := mul_le_mul_of_nonneg_left hav hk
  have hl' := mul_le_mul_of_nonneg_left he' hl
  have harg : -(v ^ 2) + (-k * v) + (-l * Real.exp (-v)) ≤ -s - k * a - l * e := by
    nlinarith only [hs, hk', hl']
  have hexp := (Real.exp_le_exp.mpr harg).trans hU
  have hnorm : 0 ≤ (Real.sqrt Real.pi)⁻¹ := (inv_nonneg.mpr (Real.sqrt_nonneg _))
  have hU0 : 0 ≤ U := (Real.exp_pos _).le.trans hU
  have hm := mul_le_mul hexp inv_sqrt_pi_le_113_div_200 hnorm hU0
  rw [Real.exp_add, Real.exp_add] at hm
  dsimp only [Analysis.normalizedGaussianWeight]
  rw [div_eq_mul_inv]
  nlinarith only [hm]

/-- Integrating the pointwise Gaussian cell bound gives cell width times the cap.
Continuity justifies the interval integral comparison. -/
theorem gaussian_density_integral_cell_upper {a b k l s e U : ℝ} (hab : a ≤ b) (hk : 0 ≤ k)
    (hl : 0 ≤ l) (hs : ∀ v ∈ Set.Icc a b, s ≤ v ^ 2) (he : e ≤ Real.exp (-b))
    (hU : Real.exp (-s - k * a - l * e) ≤ U) :
    (∫ v in a..b,
        Analysis.normalizedGaussianWeight v * Real.exp (-k * v) * Real.exp (-l * Real.exp (-v))) ≤
      (b - a) * ((113 / 200 : ℝ) * U) := by
  have hf :
    Continuous
      (fun v : ℝ ↦
        Analysis.normalizedGaussianWeight v * Real.exp (-k * v) * Real.exp (-l * Real.exp (-v))) :=
    (Analysis.continuous_normalizedGaussianWeight.mul
          (Real.continuous_exp.comp (continuous_const.mul continuous_id))).mul
      (Real.continuous_exp.comp (continuous_const.mul (Real.continuous_exp.comp continuous_id.neg)))
  have hm :=
    intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hab (hf.intervalIntegrable a b)
      (intervalIntegrable_const)
      (fun v hv ↦ gaussian_density_cell_upper hv.1 hv.2 hk hl (hs v hv) he hU)
  simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using hm

/-- On any finite ordered grid, certified cell caps bound the Gaussian integral.
Sum the interval inequalities and telescope adjacent integrals. This is the
analytic transfer for finite rational quadrature certificates. -/
theorem gaussian_density_integral_grid_upper {p s e U : ℕ → ℝ} {n : ℕ} {k l : ℝ} (hk : 0 ≤ k)
    (hl : 0 ≤ l) (hp : ∀ i < n, p i ≤ p (i + 1))
    (hs : ∀ i < n, ∀ v ∈ Set.Icc (p i) (p (i + 1)), s i ≤ v ^ 2)
    (he : ∀ i < n, e i ≤ Real.exp (-p (i + 1)))
    (hU : ∀ i < n, Real.exp (-s i - k * p i - l * e i) ≤ U i) :
    (∫ v in p 0..p n,
        Analysis.normalizedGaussianWeight v * Real.exp (-k * v) * Real.exp (-l * Real.exp (-v))) ≤
      ∑ i ∈ Finset.range n, (p (i + 1) - p i) * ((113 / 200 : ℝ) * U i) := by
  let f : ℝ → ℝ := fun v ↦
    Analysis.normalizedGaussianWeight v * Real.exp (-k * v) * Real.exp (-l * Real.exp (-v))
  have hf : Continuous f :=
    (Analysis.continuous_normalizedGaussianWeight.mul
          (Real.continuous_exp.comp (continuous_const.mul continuous_id))).mul
      (Real.continuous_exp.comp (continuous_const.mul (Real.continuous_exp.comp continuous_id.neg)))
  have hi : ∀ i < n, IntervalIntegrable f MeasureTheory.volume (p i) (p (i + 1)) := fun i _ ↦
    hf.intervalIntegrable _ _
  have h :=
    Finset.sum_le_sum
      (fun i hi ↦
        gaussian_density_integral_cell_upper (hp i (Finset.mem_range.mp hi)) hk hl
          (hs i (Finset.mem_range.mp hi)) (he i (Finset.mem_range.mp hi))
          (hU i (Finset.mem_range.mp hi)))
  change (∑ i ∈ Finset.range n, ∫ v in p i..p (i + 1), f v) ≤ _ at h
  rw [intervalIntegral.sum_integral_adjacent_intervals hi] at h
  exact h

/-- The least square on a real cell is the nearer endpoint square when the
cell has one sign, and zero when it crosses zero. This supplies the explicit
square input for rational Gaussian cell certificates. -/
noncomputable def gaussianCellSquareLower (a b : ℝ) : ℝ :=
  if b ≤ 0 then b ^ 2 else if 0 ≤ a then a ^ 2 else 0

/-- The explicit cell square lower bound holds for every point between the
endpoints. Compare endpoint squares using the corresponding sign case. -/
theorem gaussian_cell_square_lower {a b v : ℝ} (hav : a ≤ v) (hvb : v ≤ b) :
    gaussianCellSquareLower a b ≤ v ^ 2 := by
  unfold gaussianCellSquareLower
  split_ifs with hb ha
  · have hm := mul_nonneg (sub_nonneg.mpr hvb) (by linarith only [hb, hvb] : 0 ≤ -(b + v))
    nlinarith only [hm]
  · have hm := mul_nonneg (sub_nonneg.mpr hav) (by linarith only [ha, hav] : 0 ≤ v + a)
    nlinarith only [hm]
  · exact sq_nonneg v

end PseudoPrime.LLS.PaperStatements
