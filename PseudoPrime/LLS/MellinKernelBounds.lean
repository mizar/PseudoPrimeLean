/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperDefinitions
public import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# General Mellin-kernel bounds for the LLS paper

These bounds prove the summability clause of Lemma 6.1 from the kernel hypotheses.
The GRH contour formula and the uniform principal/nonprincipal estimates remain separate.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements.MellinKernel

/-- Each allowed vertical line has an integrable kernel. Use the given inverse-Mellin
integrability at argument one, where the power factor is one. This supplies line masses. -/
theorem integrable_line (K : MellinKernel) {c : ℝ} (hc : -1 / 2 < c) (hc' : c ≤ 1 / 2 + K.delta) :
    MeasureTheory.Integrable (fun t : ℝ ↦ K.function ((c : ℂ) + Complex.I * t)) := by
  have h := K.mellin_integrable c 1 hc hc' (by norm_num only)
  simpa only [Complex.ofReal_one, Complex.one_cpow, mul_one] using h

/-- For a positive real argument, the complex Mellin power has norm `u^(-c)`.
Its exponent has real part `-c`; this removes the imaginary integration parameter. -/
theorem norm_mellin_power {c u t : ℝ} (hu : 0 < u) :
    ‖(u : ℂ) ^ (-((c : ℂ) + Complex.I * t))‖ = u ^ (-c) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hu]
  simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]

/-- The inverse Mellin transform at a positive argument is bounded by the line's
absolute kernel integral times `u^(-c)/(2π)`. Move to the allowed line and apply the
integral triangle inequality. This yields polynomial decay for the Mangoldt sum. -/
theorem norm_transform_le_line (K : MellinKernel) {c u : ℝ} (hc : -1 / 2 < c)
    (hc' : c ≤ 1 / 2 + K.delta) (hu : 0 < u) :
    ‖K.transform u‖ ≤
      (1 / (2 * Real.pi)) *
        (MeasureTheory.integral MeasureTheory.volume
          (fun t : ℝ ↦ ‖K.function ((c : ℂ) + Complex.I * t)‖)) *
        u ^ (-c) := by
  rw [MellinKernel.transform, ← K.mellin_eq c u hc hc' hu, inverseMellin, norm_mul]
  have hconst : ‖((1 / (2 * Real.pi) : ℝ) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    exact one_div_nonneg.mpr (mul_nonneg (by norm_num only) Real.pi_pos.le)
  rw [hconst]
  calc
    _ ≤
        (1 / (2 * Real.pi)) *
          MeasureTheory.integral MeasureTheory.volume
            (fun t : ℝ ↦
              ‖K.function ((c : ℂ) + Complex.I * t) * (u : ℂ) ^ (-((c : ℂ) + Complex.I * t))‖) :=
      mul_le_mul_of_nonneg_left (MeasureTheory.norm_integral_le_integral_norm _)
        (one_div_nonneg.mpr (mul_nonneg (by norm_num only) Real.pi_pos.le))
    _ = _ := by
      simp only [norm_mul, norm_mellin_power hu, MeasureTheory.integral_mul_const, mul_assoc]

/-- For a positive index and argument, bound the smoothed character summand by a
constant times the norm of a twisted Mangoldt L-series term at `c+1/2`.
The Mellin norm estimate and real-power identities supply the summable majorant. -/
theorem norm_summand_le_line (K : MellinKernel) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x c : ℝ} (hx : 0 < x) (hc : -1 / 2 < c) (hc' : c ≤ 1 / 2 + K.delta) {n : ℕ} (hn : n ≠ 0) :
    ‖K.summand χ x n‖ ≤
      ((1 / (2 * Real.pi)) *
          MeasureTheory.integral MeasureTheory.volume
            (fun t : ℝ ↦ ‖K.function ((c : ℂ) + Complex.I * t)‖)) *
        x ^ c *
        ‖LSeries.term (fun n ↦ χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) ((c + 1 / 2 : ℝ) : ℂ)
            n‖ := by
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  rw [summand, ite_eq_right hn, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))]
  have hb := norm_transform_le_line K hc hc' (div_pos hnpos hx)
  calc
    _ ≤
        (ArithmeticFunction.vonMangoldt n / Real.sqrt n * ‖χ n‖) *
          (((1 / (2 * Real.pi)) *
              MeasureTheory.integral MeasureTheory.volume
                (fun t : ℝ ↦ ‖K.function ((c : ℂ) + Complex.I * t)‖)) *
            ((n : ℝ) / x) ^ (-c)) :=
      mul_le_mul_of_nonneg_left hb
        (mul_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
          (norm_nonneg _))
    _ = _ := by
      rw [LSeries.norm_term_eq, ite_eq_right hn, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, Complex.ofReal_re,
        Real.div_rpow hnpos.le hx.le, Real.rpow_neg hnpos.le, Real.rpow_neg hx.le,
        Real.sqrt_eq_rpow, Real.rpow_add hnpos]
      simp only [div_eq_mul_inv, inv_inv, mul_inv_rev]
      ring

/-- For every character and positive cutoff, the smoothed Mangoldt series is summable.
Choose the line `c=1/2+delta`, where the twisted Mangoldt L-series converges absolutely.
This proves the convergence clause of Lemma 6.1 without GRH or subgroup assumptions. -/
theorem summable_summand (K : MellinKernel) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 0 < x) : Summable (K.summand χ x) := by
  let c : ℝ := 1 / 2 + K.delta
  have hc : 1 / 2 < c := lt_add_of_pos_right _ K.delta_pos
  have hcs : 1 < ((c + 1 / 2 : ℝ) : ℂ).re := by
    rw [Complex.ofReal_re]
    linarith only [hc]
  have hs := (χ.LSeriesSummable_twist_vonMangoldt hcs).norm
  apply
    (hs.mul_left
        (((1 / (2 * Real.pi)) *
            MeasureTheory.integral MeasureTheory.volume
              (fun t : ℝ ↦ ‖K.function ((c : ℂ) + Complex.I * t)‖)) *
          x ^ c)).of_norm_bounded
  intro n
  by_cases hn : n = 0
  · subst n
    simp only [summand, ite_true, norm_zero, LSeries.term, Pi.mul_apply, ite_true, mul_zero]
    exact le_refl 0
  · exact
      norm_summand_le_line K χ hx (lt_trans (by norm_num only : (-1 : ℝ) / 2 < 1 / 2) hc)
        (le_refl _) hn

/-- The inverse Mellin transform at any positive argument has norm at most the kernel
mass on the imaginary axis. Specialize the line estimate to `c=0`.
This is the common transform bound used in the kernel comparison. -/
theorem norm_transform_le_mass (K : MellinKernel) {u : ℝ} (hu : 0 < u) :
    ‖K.transform u‖ ≤ K.mass := by
  have hc : -(1 : ℝ) / 2 < 0 := by norm_num only
  have hc' : (0 : ℝ) ≤ 1 / 2 + K.delta :=
    le_trans (by norm_num only : (0 : ℝ) ≤ 1 / 2) (le_of_lt (lt_add_of_pos_right _ K.delta_pos))
  have hb := norm_transform_le_line K hc hc' hu
  simpa only [Complex.ofReal_zero, zero_add, neg_zero, Real.rpow_zero, mul_one, MellinKernel.mass,
    div_eq_mul_inv, mul_comm, one_mul] using hb

/-- Every admissible kernel has strictly positive mass. A nonzero nonnegative real
transform value is bounded by its norm and then by the imaginary-axis mass.
This justifies division by the kernel mass in subsequent comparisons. -/
theorem mass_pos (K : MellinKernel) : 0 < K.mass := by
  obtain ⟨u, hu, hne⟩ := K.mellin_nonzero
  have hp : 0 < (K.transform u).re := lt_of_le_of_ne (K.mellin_nonneg u hu) hne.symm
  exact lt_of_lt_of_le hp ((Complex.re_le_norm (K.transform u)).trans (norm_transform_le_mass K hu))

/-- For a positive cutoff, the finite smoothed Mangoldt sums converge to the actual
infinite sum. Absolute convergence proved above supplies the `HasSum` interface,
so later contour formulas can pass from partial sums to the paper's `tsum`. -/
theorem tendsto_sum_summand (K : MellinKernel) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x : ℝ} (hx : 0 < x) :
    Filter.Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.range N, K.summand χ x n) Filter.atTop
      (nhds (∑' n : ℕ, K.summand χ x n)) := by
  exact (summable_summand K χ hx).hasSum.tendsto_sum_nat

end PseudoPrime.LLS.PaperStatements.MellinKernel
