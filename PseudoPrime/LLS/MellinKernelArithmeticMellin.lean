/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.MellinKernelContour
public import PseudoPrime.AnalyticNumberTheory.General.MellinWeights
public import PseudoPrime.Analysis.IntegralSeries
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.Basic

/-! # Arithmetic Mellin inversion for admissible kernels

Absolute convergence justifies exchanging the Mangoldt series and the
vertical integral before shifting contours in Lemma 6.1.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements.MellinKernel

/-- The vertical integrand for one smoothed Mangoldt summand. The zero
index is excluded; other indices carry `Λ(n)χ(n)/sqrt(n)` times the kernel
and the Mellin power of `n/x`. Its normalized integral recovers the summand. -/
noncomputable def arithmeticMellinTerm (K : MellinKernel) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (x c : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  if n = 0 then 0
  else
    ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * χ n *
      (K.function ((c : ℂ) + Complex.I * t) *
        (((n : ℝ) / x : ℝ) : ℂ) ^ (-((c : ℂ) + Complex.I * t)))

/-- For a positive cutoff and an admissible vertical line, each coefficient
integrand is absolutely integrable. The kernel power is integrable, and its
coefficient is constant. This supplies the termwise integral hypotheses. -/
theorem integrable_arithmeticMellinTerm (K : MellinKernel) {q : ℕ} (χ : DirichletCharacter ℂ q)
    {x c : ℝ} (hx : 0 < x) (hc : -1 / 2 < c) (hc' : c ≤ 1 / 2 + K.delta) (n : ℕ) :
    MeasureTheory.Integrable (K.arithmeticMellinTerm χ x c n) := by
  change MeasureTheory.Integrable (fun t : ℝ ↦ K.arithmeticMellinTerm χ x c n t)
  by_cases hn : n = 0
  · subst n
    simp only [arithmeticMellinTerm, ite_true]
    exact MeasureTheory.integrable_zero _ _ _
  · have hi :=
      integrable_inverse_in_strip K (by linarith only [hc, K.delta_pos]) hc' (ne_of_gt hc)
        (div_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) hx)
    simpa only [arithmeticMellinTerm, ite_eq_right hn] using
      hi.const_mul (((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * χ n)

/-- For a positive cutoff and an admissible line, the normalized integral of
each coefficient term equals the actual smoothed Mangoldt summand. Use the
kernel's Mellin-line independence and extract its constant coefficient. -/
theorem arithmeticMellinTerm_integral (K : MellinKernel) {q : ℕ} (χ : DirichletCharacter ℂ q)
    {x c : ℝ} (hx : 0 < x) (hc : -1 / 2 < c) (hc' : c ≤ 1 / 2 + K.delta) (n : ℕ) :
    K.summand χ x n =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ, K.arithmeticMellinTerm χ x c n t := by
  by_cases hn : n = 0
  · subst n
    simp only [summand, arithmeticMellinTerm, ite_true, MeasureTheory.integral_zero, mul_zero]
  · rw [summand, ite_eq_right hn, transform, ←
      K.mellin_eq c ((n : ℝ) / x) hc hc' (div_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) hx),
      inverseMellin]
    simp only [arithmeticMellinTerm, ite_eq_right hn, MeasureTheory.integral_const_mul]
    ring

/-- For a positive cutoff and nonzero index, the integral norm factors into
`x^c`, the norm of the twisted L-series term at `c+1/2`, and the kernel's
line norm integral. Real-power identities yield this summable majorant. -/
theorem integral_norm_arithmeticMellinTerm (K : MellinKernel) {q : ℕ} (χ : DirichletCharacter ℂ q)
    {x c : ℝ} (hx : 0 < x) {n : ℕ} (hn : n ≠ 0) :
    (∫ t : ℝ, ‖K.arithmeticMellinTerm χ x c n t‖) =
      x ^ c *
        ‖LSeries.term (fun n ↦ χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) ((c + 1 / 2 : ℝ) : ℂ)
            n‖ *
        (∫ t : ℝ, ‖K.function ((c : ℂ) + Complex.I * t)‖) := by
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hu := div_pos hnpos hx
  simp only [arithmeticMellinTerm, ite_eq_right hn, norm_mul, norm_mellin_power hu,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_mul_const]
  rw [LSeries.norm_term_eq, ite_eq_right hn, norm_mul]
  simp only [Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
    abs_of_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)),
    Complex.ofReal_re, Real.div_rpow hnpos.le hx.le, Real.rpow_neg hnpos.le, Real.rpow_neg hx.le,
    Real.sqrt_eq_rpow, Real.rpow_add hnpos]
  simp only [div_eq_mul_inv, inv_inv, mul_inv_rev]
  ring

/-- On a line `c>1/2` and for a positive cutoff, the coefficient integral
norms have a finite sum. Their factorization reduces this to absolute
convergence of the twisted Mangoldt L-series. This justifies integration of the series. -/
theorem summable_integral_norm_arithmeticMellinTerm (K : MellinKernel) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {x c : ℝ} (hx : 0 < x) (hc : 1 / 2 < c) :
    Summable (fun n : ℕ ↦ ∫ t : ℝ, ‖K.arithmeticMellinTerm χ x c n t‖) := by
  have hs :=
    (χ.LSeriesSummable_twist_vonMangoldt
        (by
          rw [Complex.ofReal_re]; linarith only [hc] : 1 < (((c + 1 / 2 : ℝ) : ℂ)).re)).norm
  have hh := (hs.mul_left (x ^ c)).mul_right (∫ t : ℝ, ‖K.function ((c : ℂ) + Complex.I * t)‖)
  apply hh.congr
  intro n
  by_cases hn : n = 0
  · subst n
    simp only [arithmeticMellinTerm, ite_true, norm_zero, MeasureTheory.integral_zero, LSeries.term,
      ite_true, norm_zero, mul_zero, zero_mul]
  · exact (integral_norm_arithmeticMellinTerm K χ hx hn).symm

/-- For a positive cutoff and an admissible line `c>1/2`, the smoothed
Mangoldt sum is the normalized integral of the coefficient series. Integrate
termwise using summable integral norms; no GRH or primitivity is required. -/
theorem tsum_summand_eq_integral_tsum (K : MellinKernel) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {x c : ℝ} (hx : 0 < x) (hc : 1 / 2 < c)
    (hc' : c ≤ 1 / 2 + K.delta) :
    (∑' n : ℕ, K.summand χ x n) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ, ∑' n : ℕ, K.arithmeticMellinTerm χ x c n t := by
  have hc0 : -1 / 2 < c := lt_trans (by norm_num only) hc
  rw [tsum_congr (arithmeticMellinTerm_integral K χ hx hc0 hc'), tsum_mul_left]
  rw [(MeasureTheory.hasSum_integral_of_summable_integral_norm
        (integrable_arithmeticMellinTerm K χ hx hc0 hc')
        (summable_integral_norm_arithmeticMellinTerm K χ hx hc)).tsum_eq]

/-- For a positive cutoff, each coefficient integrand is an L-series term
at `s+1/2` times `K(s)x^s`. Split the power of `n/x` and absorb `sqrt(n)`
into the shifted exponent. The zero-index branch agrees with the L-series convention. -/
theorem arithmeticMellinTerm_eq_LSeries_term (K : MellinKernel) {q : ℕ} (χ : DirichletCharacter ℂ q)
    {x : ℝ} (hx : 0 < x) (c : ℝ) (n : ℕ) (t : ℝ) :
    K.arithmeticMellinTerm χ x c n t =
      LSeries.term (fun n ↦ χ n * (ArithmeticFunction.vonMangoldt n : ℂ))
          (((c : ℂ) + Complex.I * t) + 1 / 2) n *
        (K.function ((c : ℂ) + Complex.I * t) * (x : ℂ) ^ ((c : ℂ) + Complex.I * t)) := by
  by_cases hn : n = 0
  · subst n
    simp only [arithmeticMellinTerm, ite_true, LSeries.term, ite_true, zero_mul]
  · have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hnz : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    rw [arithmeticMellinTerm, ite_eq_right hn, LSeries.term, ite_eq_right hn]
    rw [AnalyticNumberTheory.General.cpow_div_eq_cpow_mul_cpow_neg hnpos.le hx, neg_neg]
    rw [Complex.ofReal_div, Real.sqrt_eq_rpow, Complex.ofReal_cpow hnpos.le, Complex.ofReal_div,
      Complex.ofReal_one, Complex.ofReal_ofNat, Complex.ofReal_natCast, Complex.cpow_add _ _ hnz,
      Complex.cpow_neg]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring

/-- For a positive cutoff, the full coefficient integrand is the twisted
Mangoldt L-series at `s+1/2` times `K(s)x^s`. The identity holds without
convergence assumptions, by the definition of the L-series and multiplication of a tsum. -/
theorem tsum_arithmeticMellinTerm (K : MellinKernel) {q : ℕ} (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 0 < x) (c t : ℝ) :
    (∑' n : ℕ, K.arithmeticMellinTerm χ x c n t) =
      LSeries (fun n ↦ χ n * (ArithmeticFunction.vonMangoldt n : ℂ))
          (((c : ℂ) + Complex.I * t) + 1 / 2) *
        (K.function ((c : ℂ) + Complex.I * t) * (x : ℂ) ^ ((c : ℂ) + Complex.I * t)) := by
  rw [tsum_congr (fun n ↦ arithmeticMellinTerm_eq_LSeries_term K χ hx c n t), tsum_mul_right]
  rfl

/-- For a positive cutoff and an admissible line `c>1/2`, the smoothed
Mangoldt sum equals the vertical integral of its twisted L-series times
`K(s)x^s`. Combine termwise inversion, absolute convergence, and the series identity. -/
theorem tsum_summand_eq_integral_LSeries (K : MellinKernel) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {x c : ℝ} (hx : 0 < x) (hc : 1 / 2 < c)
    (hc' : c ≤ 1 / 2 + K.delta) :
    (∑' n : ℕ, K.summand χ x n) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ,
          LSeries (fun n ↦ χ n * (ArithmeticFunction.vonMangoldt n : ℂ))
              (((c : ℂ) + Complex.I * t) + 1 / 2) *
            (K.function ((c : ℂ) + Complex.I * t) * (x : ℂ) ^ ((c : ℂ) + Complex.I * t)) := by
  rw [tsum_summand_eq_integral_tsum K χ hx hc hc']
  congr 1
  exact
    MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall (tsum_arithmeticMellinTerm K χ hx c))

open AnalyticNumberTheory.DirichletLFunction in
/-- For a positive cutoff and a line `c>1/2`, the coefficient series equals
`-L'/L(s+1/2)K(s)x^s`. The Euler-product identity rewrites the shifted
L-series. This pointwise equality supports both integration and integrability. -/
theorem tsum_arithmeticMellinTerm_eq_logDeriv (K : MellinKernel) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {x c : ℝ} (hx : 0 < x) (hc : 1 / 2 < c) (t : ℝ) :
    (∑' n : ℕ, K.arithmeticMellinTerm χ x c n t) =
      -logDeriv (DirichletCharacter.LFunction χ) (((c : ℂ) + Complex.I * t) + 1 / 2) *
        (K.function ((c : ℂ) + Complex.I * t) * (x : ℂ) ^ ((c : ℂ) + Complex.I * t)) := by
  rw [tsum_arithmeticMellinTerm K χ hx c t,
    lSeries_twist_vonMangoldt_eq_neg_logDeriv_dirichletLFunction_of_one_lt_re χ
      (by
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero, Complex.div_ofNat_re,
          Complex.one_re]
        linarith only [hc])]
  simp only [logDeriv, Pi.div_apply, neg_div]

/-- For a positive cutoff and an admissible line `c>1/2`, the arithmetic
logarithmic-derivative integrand is absolutely integrable. Summable coefficient
integral norms supply integrability of the series, then its pointwise identity
transfers it to `-L'/L`. This validates the right-hand contour integral. -/
theorem integrable_arithmeticMellin_logDeriv (K : MellinKernel) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {x c : ℝ} (hx : 0 < x) (hc : 1 / 2 < c)
    (hc' : c ≤ 1 / 2 + K.delta) :
    MeasureTheory.Integrable
      (fun t : ℝ ↦
        -logDeriv (DirichletCharacter.LFunction χ) (((c : ℂ) + Complex.I * t) + 1 / 2) *
          (K.function ((c : ℂ) + Complex.I * t) * (x : ℂ) ^ ((c : ℂ) + Complex.I * t))) := by
  have hi :=
    Analysis.integrable_tsum_of_summable_integral_norm (K.arithmeticMellinTerm χ x c)
      (integrable_arithmeticMellinTerm K χ hx (lt_trans (by norm_num only) hc) hc')
      (summable_integral_norm_arithmeticMellinTerm K χ hx hc)
  exact hi.congr (Filter.Eventually.of_forall (tsum_arithmeticMellinTerm_eq_logDeriv K χ hx hc))

/-- For any character, positive cutoff, and admissible line `c>1/2`, the
smoothed Mangoldt sum is the normalized integral of `-L'/L(s+1/2)K(s)x^s`.
The Euler-series identity converts the proved arithmetic integral formula.
This is the right-hand contour identity used in Lemma 6.1. -/
theorem tsum_summand_eq_integral_logDeriv (K : MellinKernel) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {x c : ℝ} (hx : 0 < x) (hc : 1 / 2 < c)
    (hc' : c ≤ 1 / 2 + K.delta) :
    (∑' n : ℕ, K.summand χ x n) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ,
          -logDeriv (DirichletCharacter.LFunction χ) (((c : ℂ) + Complex.I * t) + 1 / 2) *
            (K.function ((c : ℂ) + Complex.I * t) * (x : ℂ) ^ ((c : ℂ) + Complex.I * t)) := by
  rw [tsum_summand_eq_integral_tsum K χ hx hc hc']
  congr 1
  exact
    MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall (tsum_arithmeticMellinTerm_eq_logDeriv K χ hx hc))

end PseudoPrime.LLS.PaperStatements.MellinKernel
