/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ReciprocalGapLeftReflection
public import PseudoPrime.AnalyticNumberTheory.General.WeightedDirichletIntegrals

/-! # Exact reflected Euler integrals for the adjustable two-pole kernel -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For nonzero coefficient index and positive scale, factor the reflected Dirichlet term
into a fixed coefficient and Mellin power at scale n*x. Use the complex power quotient law.
This prepares exact integration without taking separate norms. -/
theorem reflected_term_factor (f : ℕ → ℂ) {n : ℕ} (hn : n ≠ 0) {x : ℝ} (hx : 0 < x) (s : ℂ) :
    LSeries.term f (1 / 2 - s) n * (x : ℂ) ^ s =
      (f n / (n : ℂ) ^ (1 / 2 : ℂ)) * (((n : ℝ) * x : ℝ) : ℂ) ^ s := by
  have hnz : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  simp only [LSeries.term, ite_eq_right hn, Complex.cpow_sub _ _ hnz, Complex.ofReal_mul]
  rw [Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg n) hx.le]
  simp only [Complex.ofReal_natCast, div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

/-- For a positive gap, a line between the poles and scale at least one, integrate each
nonzero reflected Dirichlet term exactly. Factor its fixed coefficient and invert at n*x.
The negative middle-strip profile supplies the signed value. -/
theorem reflected_term_integral (f : ℕ → ℂ) {n : ℕ} (hn : n ≠ 0) {h c x : ℝ} (hh : 0 < h)
    (hcl : -1 / 2 - h < c) (hcu : c < -1 / 2) (hx : 1 ≤ x) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          LSeries.term f (1 / 2 - ((c : ℂ) + Complex.I * t)) n *
            (Analysis.reciprocalGapFunction h ((c : ℂ) + Complex.I * t) *
              (x : ℂ) ^ ((c : ℂ) + Complex.I * t))) =
      (f n / (n : ℂ) ^ (1 / 2 : ℂ)) * ((-((n : ℝ) * x) ^ (-1 / 2 - h) / h : ℝ) : ℂ) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hnx : 1 ≤ (n : ℝ) * x := by
    nlinarith only [mul_le_mul_of_nonneg_right hn1 (zero_lt_one.trans_le hx).le, hx]
  have he (t : ℝ) :
    LSeries.term f (1 / 2 - ((c : ℂ) + Complex.I * t)) n *
        (Analysis.reciprocalGapFunction h ((c : ℂ) + Complex.I * t) *
          (x : ℂ) ^ ((c : ℂ) + Complex.I * t)) =
      (f n / (n : ℂ) ^ (1 / 2 : ℂ)) *
        (Analysis.reciprocalGapFunction h ((c : ℂ) + Complex.I * t) *
          (((n : ℝ) * x : ℝ) : ℂ) ^ ((c : ℂ) + Complex.I * t)) := by
    calc
      _ =
          Analysis.reciprocalGapFunction h ((c : ℂ) + Complex.I * t) *
            (LSeries.term f (1 / 2 - ((c : ℂ) + Complex.I * t)) n *
              (x : ℂ) ^ ((c : ℂ) + Complex.I * t)) :=
        by ring
      _ = _ := by
        rw [reflected_term_factor f hn (zero_lt_one.trans_le hx)]; ring
  rw [MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ he),
    MeasureTheory.integral_const_mul, mul_left_comm,
    reciprocalGap_left_kernel_integral hh hcl hcu hnx]

/-- For nonzero index and positive scale, rewrite the exact reflected coefficient as
-x^(-1/2-h)/h times the Dirichlet term at 1+h. Combine real and complex powers.
This identifies the real Euler evaluation point after integration. -/
theorem reflected_coefficient (f : ℕ → ℂ) {n : ℕ} (hn : n ≠ 0) {h x : ℝ} (hx : 0 < x) :
    (f n / (n : ℂ) ^ (1 / 2 : ℂ)) * ((-((n : ℝ) * x) ^ (-1 / 2 - h) / h : ℝ) : ℂ) =
      ((-x ^ (-1 / 2 - h) / h : ℝ) : ℂ) * LSeries.term f ((1 + h : ℝ) : ℂ) n := by
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hnz : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hp :
    (n : ℂ) ^ ((-1 / 2 - h : ℝ) : ℂ) = (n : ℂ) ^ (1 / 2 : ℂ) / (n : ℂ) ^ ((1 + h : ℝ) : ℂ) := by
    rw [← Complex.cpow_sub _ _ hnz]
    congr 1
    push_cast
    ring
  rw [Real.mul_rpow hn0.le hx.le]
  simp only [Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_cpow hn0.le,
    Complex.ofReal_natCast]
  rw [hp]
  simp only [LSeries.term, ite_eq_right hn]
  have hz : (n : ℂ) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    exact fun he ↦ hnz he.1
  field_simp [hz]

/-- For a positive gap, a line between the poles, scale at least one and absolute
Dirichlet convergence at 1/2-c, the reflected series integral equals the signed factor
-x^(-1/2-h)/h times the series at 1+h. Exchange integrals and sums using an integrable
kernel weight, then integrate every term exactly. No character assumptions are needed. -/
theorem reflected_LSeries_integral {f : ℕ → ℂ} {h c x : ℝ} (hh : 0 < h) (hcl : -1 / 2 - h < c)
    (hcu : c < -1 / 2) (hx : 1 ≤ x) (hs : LSeriesSummable f ((1 / 2 - c : ℝ) : ℂ)) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          LSeries f (1 / 2 - ((c : ℂ) + Complex.I * t)) *
            (Analysis.reciprocalGapFunction h ((c : ℂ) + Complex.I * t) *
              (x : ℂ) ^ ((c : ℂ) + Complex.I * t))) =
      ((-x ^ (-1 / 2 - h) / h : ℝ) : ℂ) * LSeries f ((1 + h : ℝ) : ℂ) := by
  let W := fun t : ℝ ↦
    Analysis.reciprocalGapFunction h ((c : ℂ) + Complex.I * t) * (x : ℂ) ^ ((c : ℂ) + Complex.I * t)
  have hiW : MeasureTheory.Integrable W :=
    integrable_reciprocalGap_middle_kernel hcl hcu (zero_lt_one.trans_le hx)
  have he (t : ℝ) :
    1 / 2 - ((c : ℂ) + Complex.I * t) = ((1 / 2 - c : ℝ) : ℂ) + Complex.I * (-t : ℝ) := by
    push_cast; ring
  have hi :=
    AnalyticNumberTheory.General.integral_LSeries_mul_weight_eq_tsum hs (fun t : ℝ ↦ -t) W
      continuous_neg hiW
  simp only [← he] at hi
  change
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, LSeries f (1 / 2 - ((c : ℂ) + Complex.I * t)) * W t) =
      _
  rw [hi, ← tsum_mul_left]
  change _ = ((-x ^ (-1 / 2 - h) / h : ℝ) : ℂ) * ∑' n : ℕ, LSeries.term f ((1 + h : ℝ) : ℂ) n
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · subst n
    simp only [LSeries.term_zero, zero_mul, MeasureTheory.integral_zero, mul_zero]
  · exact
      (reflected_term_integral f hn hh hcl hcu hx).trans
        (reflected_coefficient f hn (zero_lt_one.trans_le hx))

open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/-- For any character, positive gap, line between the poles and scale at least one,
the reflected ordinary logarithmic derivative integral equals -x^(-1/2-h)/h times
its value at 1+h. Use the absolutely convergent Mangoldt series and exact term integration.
This removes the near-pole distance loss from the reflected Euler contribution; it does
not evaluate the reflected Gamma contribution, and does not require GRH. -/
theorem reflected_logDeriv_integral {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {h c x : ℝ}
    (hh : 0 < h) (hcl : -1 / 2 - h < c) (hcu : c < -1 / 2) (hx : 1 ≤ x) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          logDeriv χ.LFunction (1 / 2 - ((c : ℂ) + Complex.I * t)) *
            (Analysis.reciprocalGapFunction h ((c : ℂ) + Complex.I * t) *
              (x : ℂ) ^ ((c : ℂ) + Complex.I * t))) =
      ((-x ^ (-1 / 2 - h) / h : ℝ) : ℂ) * logDeriv χ.LFunction ((1 + h : ℝ) : ℂ) := by
  let f := fun n : ℕ ↦ χ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ)
  have he {s : ℂ} (hr : 1 < s.re) : logDeriv χ.LFunction s = -LSeries f s := by
    have hv := lSeries_twist_vonMangoldt_eq_neg_logDeriv_dirichletLFunction_of_one_lt_re χ hr
    change LSeries f s = -deriv χ.LFunction s / χ.LFunction s at hv
    change deriv χ.LFunction s / χ.LFunction s = -LSeries f s
    rw [hv]
    ring
  have hr : 1 < (((1 / 2 - c : ℝ) : ℂ)).re := by
    rw [Complex.ofReal_re]
    linarith only [hcu]
  have hs := DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hr
  change LSeriesSummable f ((1 / 2 - c : ℝ) : ℂ) at hs
  have hi := reflected_LSeries_integral hh hcl hcu hx hs
  have hp (t : ℝ) : 1 < (1 / 2 - ((c : ℂ) + Complex.I * t)).re := by
    simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re, Complex.add_re,
      Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul,
      mul_zero, sub_zero, add_zero]
    linarith only [hcu]
  simp only [he (hp _), neg_mul, MeasureTheory.integral_neg]
  rw [mul_neg, hi,
    he
      (by
        rw [Complex.ofReal_re]; linarith only [hh])]
  ring

end PseudoPrime.LLS.PaperStatements
