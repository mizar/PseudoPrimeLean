/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TriangularZeroMassBounds

/-! # Explicit finite-conductor zero mass for the alpha-18 triangular kernel

Bound the scale-one arithmetic sum on the Euler-series right line.
The resulting additive zero-mass constant applies to every positive scale.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For every character of nonzero modulus, the alpha-18 scale-one arithmetic
sum has norm at most 200000000000000. Use the exact right-line Euler-series
identity, ordinary logarithmic derivative bound 272, fixed kernel decay,
the Cauchy integral pi, and Mellin normalization at most one sixth.
This removes the final arithmetic input from the finite-conductor zero bound. -/
theorem triangular18_scale_one_arithmetic_norm_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
    ‖∑' n : ℕ, K.summand χ 1 n‖ ≤ (200000000000000 : ℝ) := by
  let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
  let F := fun t : ℝ ↦
    -logDeriv χ.LFunction (((9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2) *
      K.function (((9 / 16 : ℝ) : ℂ) + Complex.I * t)
  have hb (t : ℝ) : ‖F t‖ ≤ (272 * 1000000000000 : ℝ) * (1 + t ^ 2)⁻¹ := by
    have ho :=
      AnalyticNumberTheory.DirichletLFunction.norm_logDeriv_le_inv_gap χ
        (by norm_num only : (1 : ℝ) < 17 / 16) t
    norm_num only at ho
    rw [mul_comm (t : ℂ) Complex.I] at ho
    have he :
      (((9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2) = (((17 / 16 : ℝ) : ℂ) + Complex.I * t) := by
      norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat]
      ring
    have hs : |(((9 / 16 : ℝ) : ℂ) + Complex.I * t).re| = (9 / 16 : ℝ) := by
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
      norm_num only
    have hK := Analysis.triangular18_fixed_line_decay hs
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, one_mul, zero_mul, zero_add] at hK
    dsimp only [F]
    rw [norm_mul, norm_neg, he]
    have h := mul_le_mul ho hK (norm_nonneg _) (by norm_num only : (0 : ℝ) ≤ 272)
    simpa only [K, triangularMellinKernel, div_eq_mul_inv, mul_assoc] using h
  have hraw :=
    MeasureTheory.norm_integral_le_of_norm_le
      (integrable_inv_one_add_sq.const_mul (272 * 1000000000000 : ℝ))
      (Filter.Eventually.of_forall hb)
  rw [MeasureTheory.integral_const_mul, integral_univ_inv_one_add_sq] at hraw
  have hraw' : ‖∫ t : ℝ, F t‖ ≤ (1088000000000000 : ℝ) := by nlinarith only [hraw, Real.pi_lt_four]
  have hn := norm_mellinNormalization_mul_le_sixth hraw'
  have he :=
    MellinKernel.tsum_summand_eq_integral_logDeriv K χ (x := 1) (c := 9 / 16) (by norm_num only)
      (by norm_num only)
      (by
        change (9 / 16 : ℝ) ≤ 1 / 2 + 1 / 8; norm_num only)
  simp only [Complex.ofReal_one, Complex.one_cpow, mul_one] at he
  change ‖∑' n : ℕ, K.summand χ 1 n‖ ≤ _
  rw [he]
  have hnum : (1088000000000000 : ℝ) / 6 ≤ 200000000000000 := by norm_num only
  exact hn.trans hnum

/-- For primitive nonprincipal GRH data of modulus at least two and
nonprincipal inverse, the actual alpha-18 absolute zero mass is at most
36*log(q)+1350000000000000. Insert the scale-one arithmetic estimate into the
conductor formula with explicit reflected and gamma constants and zero pole.
This is an additive finite-conductor zero-mass contract with no extra analytic inputs. -/
theorem triangular18_absoluteMass_le_explicit {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
    (∑' ρ : ℂ, ‖K.kernelZeroTerm χ ρ‖) ≤ 36 * Real.log q + 1350000000000000 := by
  let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
  have hZ := triangular18_absoluteMass_le_conductor_add_arithmetic hq hGRH hp hne hinv
  change
    (∑' ρ : ℂ, ‖K.kernelZeroTerm χ ρ‖) ≤
      36 * Real.log q + |(∑' n : ℕ, K.summand χ 1 n).re| + 1150000000000000 at hZ
  have hS := triangular18_scale_one_arithmetic_norm_le χ
  change ‖∑' n : ℕ, K.summand χ 1 n‖ ≤ (200000000000000 : ℝ) at hS
  have hA := (Complex.abs_re_le_norm (∑' n : ℕ, K.summand χ 1 n)).trans hS
  change (∑' ρ : ℂ, ‖K.kernelZeroTerm χ ρ‖) ≤ _
  linarith only [hZ, hA]

/-- For the same primitive nonprincipal GRH data and every positive scale,
the alpha-18 oscillating zero sum has norm at most 36*log(q)+1350000000000000.
Absolute convergence and the unit-norm phase reduce it to the proved actual
absolute zero mass. This supplies the zero term in explicit subgroup comparisons. -/
theorem triangular18_oscillatingZeroSum_norm_le_explicit {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) :
    let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
    ‖∑' ρ : ℂ, K.oscillatingZeroTerm χ x ρ‖ ≤ 36 * Real.log q + 1350000000000000 := by
  let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
  have hs := MellinKernel.summable_oscillatingZeroTerm K hq hGRH hp hne hinv hx
  calc
    _ ≤ ∑' ρ : ℂ, ‖K.oscillatingZeroTerm χ x ρ‖ := norm_tsum_le_tsum_norm hs.norm
    _ = ∑' ρ : ℂ, ‖K.kernelZeroTerm χ ρ‖ :=
      tsum_congr (MellinKernel.norm_oscillatingZeroTerm K χ hx)
    _ ≤ _ := triangular18_absoluteMass_le_explicit hq hGRH hp hne hinv

end PseudoPrime.LLS.PaperStatements
