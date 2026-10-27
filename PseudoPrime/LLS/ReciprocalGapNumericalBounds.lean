/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ReciprocalGapLeftBounds
public import PseudoPrime.Analysis.LogarithmicIntegralNumerics

/-! # Numerical contour budgets for adjustable reciprocal kernels -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- The fixed logarithmic moment is nonnegative, since its integrand and normalization
are nonnegative. This permits multiplication by explicit contour budgets. -/
theorem reciprocalLogMoment_nonneg : 0 ≤ reciprocalLogMoment := by
  apply
    mul_nonneg (div_nonneg zero_le_one (mul_pos (by norm_num only : (0 : ℝ) < 2) Real.pi_pos).le)
  apply MeasureTheory.integral_nonneg
  intro t
  exact
    div_nonneg (add_nonneg (Real.log_nonneg (by linarith only [abs_nonneg t])) zero_le_one)
      (by linarith only [sq_nonneg t])

/-- The fixed logarithmic moment is at most 11/3. Use the whole-line integral at most 22
and pi>3. This removes the remaining universal integral from left-contour bounds. -/
theorem reciprocalLogMoment_le_eleven_thirds : reciprocalLogMoment ≤ 11 / 3 := by
  have hJ :=
    mul_le_mul_of_nonneg_left Analysis.logarithmic_inverseSquare_integral_le_twenty_two
      (div_nonneg zero_le_one (mul_pos (by norm_num only : (0 : ℝ) < 2) Real.pi_pos).le)
  unfold reciprocalLogMoment
  apply hJ.trans
  rw [div_mul_eq_mul_div, div_le_iff₀ (mul_pos (by norm_num only : (0 : ℝ) < 2) Real.pi_pos)]
  nlinarith only [Real.pi_gt_three]

/-- For every positive gap and scale, the normalized central Gamma integral has norm at most
176 for every character. Its integrand is bounded by 48 times the common logarithmic
inverse-square profile; the integral is at most 22 and normalization is at most 1/6.
This supplies a numerical archimedean constant uniform in the gap. -/
theorem reciprocalGap_central_gamma_norm_le_numeric {h : ℝ} (hh : 0 < h) {q : ℕ}
    (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 0 < x) :
    ‖((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) *
              (Analysis.reciprocalGapFunction h (Complex.I * t) * (x : ℂ) ^ (Complex.I * t)))‖ ≤
      176 := by
  have hi :=
    MeasureTheory.norm_integral_le_of_norm_le (f := fun t : ℝ ↦
      logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) *
        (Analysis.reciprocalGapFunction h (Complex.I * t) * (x : ℂ) ^ (Complex.I * t)))
      (Analysis.integrable_log_add_abs_div_one_add_sq.const_mul (48 : ℝ))
      (MeasureTheory.ae_of_all _
        (fun t : ℝ ↦ by
          have hr : (Complex.I * (t : ℂ) + 1 / 2).re = (1 / 2 : ℝ) := by
            simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
              Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero,
              Complex.div_ofNat_re, Complex.one_re, zero_add]
          have hg :=
            AnalyticNumberTheory.DirichletLFunction.norm_logDeriv_gammaFactor_positive_strip_le_log
              χ (le_of_eq hr.symm)
              (by
                rw [hr]; norm_num only)
          have hL : 0 ≤ Real.log (4 + |t|) := Real.log_nonneg (by linarith only [abs_nonneg t])
          simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
            Complex.ofReal_im, one_mul, zero_mul, zero_add, Complex.div_ofNat_im, Complex.one_im,
            zero_div, add_zero] at hg
          have hb :
            ‖logDeriv χ.gammaFactor (Complex.I * t + 1 / 2)‖ ≤ 12 * (Real.log (4 + |t|) + 1) := by
            linarith only [hg, hL]
          rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
          simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
            Complex.ofReal_im, zero_mul, mul_zero, sub_zero, Real.rpow_zero, mul_one]
          have h :=
            mul_le_mul hb (reciprocalGap_central_norm_le hh.le t) (norm_nonneg _)
              (by linarith only [hL] : 0 ≤ 12 * (Real.log (4 + |t|) + 1))
          exact h.trans_eq (by ring)))
  rw [MeasureTheory.integral_const_mul] at hi
  have hraw :=
    hi.trans
      (mul_le_mul_of_nonneg_left Analysis.logarithmic_inverseSquare_integral_le_twenty_two
        (by norm_num only : (0 : ℝ) ≤ 48))
  have hd : ‖((1 / (2 * Real.pi) : ℝ) : ℂ)‖ ≤ (1 / 6 : ℝ) := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (div_pos zero_lt_one (mul_pos (by norm_num only : (0 : ℝ) < 2) Real.pi_pos))]
    exact one_div_le_one_div_of_le (by norm_num only) (by linarith only [Real.pi_gt_three])
  rw [norm_mul]
  have h := mul_le_mul hd hraw (norm_nonneg _) (by norm_num only : (0 : ℝ) ≤ 1 / 6)
  norm_num only at h
  exact h

/-- For scales at least one and admissible nonnegative right lines, the normalized Gamma
integral has norm at most 176 uniformly in the gap and character.
Shift the line to the center and apply the numerical bound. -/
theorem reciprocalGap_gamma_norm_le_numeric {h : ℝ} (hh : 0 < h) {q : ℕ}
    (χ : DirichletCharacter ℂ q) {x b : ℝ} (hx : 1 ≤ x) (hb0 : 0 ≤ b)
    (hbK : b ≤ 1 / 2 + (reciprocalGapMellinKernel h hh).delta) (hb2 : b ≤ 3 / 2) :
    ‖((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            logDeriv χ.gammaFactor (((b : ℂ) + Complex.I * t) + 1 / 2) *
              ((reciprocalGapMellinKernel h hh).function ((b : ℂ) + Complex.I * t) *
                (x : ℂ) ^ ((b : ℂ) + Complex.I * t)))‖ ≤
      176 := by
  rw [MellinKernel.gammaIntegral_eq_central (reciprocalGapMellinKernel h hh) χ hb0 hbK hb2 hx]
  exact reciprocalGap_central_gamma_norm_le_numeric hh χ (zero_lt_one.trans_le hx)

/-- For positive gap and scale at least one, the completed remainder minus its first-pole
residue and left integral has norm at most 176. Unfold the exact contour decomposition
and apply the numerical right-Gamma estimate. No GRH is needed for this component. -/
theorem reciprocalGap_remainder_sub_pole_left_norm_le_numeric {h : ℝ} (hh : 0 < h) {q : ℕ}
    [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 1 ≤ x) :
    ‖reciprocalGapCompletedRemainder h hh χ x -
          MellinKernel.weightedResidue (reciprocalGapMellinKernel h hh)
            (fun z : ℂ ↦ χ.completedLFunction (z + 1 / 2)) x (-1 / 2) -
          reciprocalGapLeftIntegral h hh χ x‖ ≤
      176 := by
  let K := reciprocalGapMellinKernel h hh
  have hd := K.delta_pos
  have hu : K.delta ≤ (1 / 8 : ℝ) := min_le_right _ _
  have hg :=
    reciprocalGap_gamma_norm_le_numeric hh χ (b := 1 / 2 + K.delta / 2) hx (by linarith only [hd])
      (by linarith only [hd]) (by linarith only [hu])
  have he :
    reciprocalGapCompletedRemainder h hh χ x -
        MellinKernel.weightedResidue K (fun z : ℂ ↦ χ.completedLFunction (z + 1 / 2)) x (-1 / 2) -
        reciprocalGapLeftIntegral h hh χ x =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          logDeriv χ.gammaFactor ((((1 / 2 + K.delta / 2 : ℝ) : ℂ) + Complex.I * t) + 1 / 2) *
            (K.function (((1 / 2 + K.delta / 2 : ℝ) : ℂ) + Complex.I * t) *
              (x : ℂ) ^ (((1 / 2 + K.delta / 2 : ℝ) : ℂ) + Complex.I * t))) := by
    dsimp only [reciprocalGapCompletedRemainder, reciprocalGapLeftIntegral, K]
    ring
  rw [he]
  exact hg

/-- The numerical left-contour budget replaces the logarithmic moment by 11/3.
For e=delta(h)/2 it is (11/3)*(3+6/(e*h))*(log(q)+e^(-2)+e^(-1)+12)*x^(-1/2-e).
It is used for positive gaps, levels at least one and positive scales. -/
noncomputable def reciprocalGapNumericLeftBudget (h : ℝ) (hh : 0 < h) (q : ℕ) (x : ℝ) : ℝ :=
  let e := (reciprocalGapMellinKernel h hh).delta / 2
  (11 / 3 : ℝ) * (3 + 6 / (e * h)) * (Real.log q + e⁻¹ ^ 2 + e⁻¹ + 12) * x ^ (-1 / 2 - e)

/-- For positive gap and scale and level at least one, the moment-based left budget is
bounded by the numerical budget. Multiply the moment bound by nonnegative factors.
This connects the exact left-contour theorem to a fully specified elementary expression. -/
theorem reciprocalGapLeftBudget_le_numeric {h : ℝ} (hh : 0 < h) {q : ℕ} (hq : 1 ≤ q) {x : ℝ}
    (hx : 0 < x) : reciprocalGapLeftBudget h hh q x ≤ reciprocalGapNumericLeftBudget h hh q x := by
  let e := (reciprocalGapMellinKernel h hh).delta / 2
  have he : 0 < e := half_pos (reciprocalGapMellinKernel h hh).delta_pos
  have hlog : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  have hB : 0 ≤ 3 + 6 / (e * h) :=
    add_nonneg (by norm_num only) (div_nonneg (by norm_num only) (mul_pos he hh).le)
  have hU : 0 ≤ Real.log q + e⁻¹ ^ 2 + e⁻¹ + 12 :=
    add_nonneg (add_nonneg (add_nonneg hlog (sq_nonneg _)) (inv_nonneg.mpr he.le))
      (by norm_num only)
  exact
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right reciprocalLogMoment_le_eleven_thirds hB) hU)
      (Real.rpow_nonneg hx.le _)

/-- For primitive nonprincipal GRH data with nonprincipal inverse and level at least eight,
the completed remainder norm is at most the explicit pole budget plus the numerical left
budget plus 176. Use the triangle inequality and the proved component bounds.
All contour integrals and unspecified constants have been removed. -/
theorem reciprocalGap_remainder_norm_le_numeric {h : ℝ} (hh : 0 < h) {q : ℕ} [NeZero q] (hq : 8 ≤ q)
    {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 1 ≤ x) :
    ‖reciprocalGapCompletedRemainder h hh χ x‖ ≤
      ((7 / 6 : ℝ) * Real.log q + 4) / (h * Real.sqrt x) + reciprocalGapNumericLeftBudget h hh q x +
        176 := by
  let P :=
    MellinKernel.weightedResidue (reciprocalGapMellinKernel h hh)
      (fun z : ℂ ↦ χ.completedLFunction (z + 1 / 2)) x (-1 / 2)
  let L := reciprocalGapLeftIntegral h hh χ x
  let R := reciprocalGapCompletedRemainder h hh χ x
  have he : R = (R - P - L) + P + L := by ring
  have hn :=
    (norm_add_le ((R - P - L) + P) L).trans (add_le_add (norm_add_le (R - P - L) P) (le_refl ‖L‖))
  have hγ : ‖R - P - L‖ ≤ 176 := reciprocalGap_remainder_sub_pole_left_norm_le_numeric hh χ hx
  have hpole : ‖P‖ ≤ ((7 / 6 : ℝ) * Real.log q + 4) / (h * Real.sqrt x) :=
    reciprocalGap_poleResidue_norm_le hh hq hp hne hGRH (zero_lt_one.trans_le hx)
  have hq1 : 1 ≤ q := (by norm_num only : 1 ≤ 8).trans hq
  have hL : ‖L‖ ≤ reciprocalGapNumericLeftBudget h hh q x :=
    (reciprocalGap_leftIntegral_norm_le hh hq1 hp hne hinv (zero_lt_one.trans_le hx)).trans
      (reciprocalGapLeftBudget_le_numeric hh hq1 (zero_lt_one.trans_le hx))
  rw [← he] at hn
  change ‖R‖ ≤ _
  linarith only [hn, hγ, hpole, hL]

/-- For primitive nonprincipal GRH data at level at least eight, a strict gap between the
principal finite sum and the zero-prefix budget plus explicit pole cost, numerical left
budget and 176 yields a prime non-one witness below the scale.
Apply exact witness separation after the numerical remainder bound.
This is a numerical criterion, not a certified new global witness cutoff. -/
theorem exists_prime_not_one_of_reciprocalGap_numeric_separation {h c : ℝ} (hh : 0 < h) {q : ℕ}
    [NeZero q] (hq : 8 ≤ q) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hc : (1 / 2 : ℝ) < c) (hbound : c ^ 2 ≤ 1 / 4 + h / 2) {x : ℝ}
    (hx : 1 ≤ x) (B : Finset ℕ)
    (hgap :
      (1 / c) *
            (Real.log q / 2 + (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + c) : ℂ)).re +
                (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 / 2 + c)) -
              ∑ n ∈ B, (1 + (χ n).re) * ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 / 2 + c)) +
          (((7 / 6 : ℝ) * Real.log q + 4) / (h * Real.sqrt x) +
            reciprocalGapNumericLeftBudget h hh q x +
            176) <
        (reciprocalGapCharacterSum h (1 : DirichletCharacter ℂ 1) x).re) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ x ∧ χ p ≠ 1 := by
  apply
    exists_prime_not_one_of_reciprocalGap_separation hh ((by norm_num only : 2 ≤ 8).trans hq) hGRH
      hp hne hinv hc hbound hx B
  have hr :=
    (Complex.re_le_norm (reciprocalGapCompletedRemainder h hh χ x)).trans
      (reciprocalGap_remainder_norm_le_numeric hh hq hp hne hinv hGRH hx)
  exact (add_le_add (le_refl _) hr).trans_lt hgap

end PseudoPrime.LLS.PaperStatements
