/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinateInterpolation
public import PseudoPrime.Analysis.ScaledRationalPhase

/-! # Rational certificates for ordinate phase samples -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Exact rational value of a signed zero term from a rational ordinate
and rational complex approximation to its unit phase. -/
def rationalOrdinateSample (q : ℚ) (w : ℚ × ℚ) : ℚ :=
  2 * (w.1 / 2 + q * w.2) / (1 / 4 + q ^ 2)

/-- Casting the rational sample gives the corresponding real part of the
complex quotient by the critical-line denominator. -/
theorem rationalOrdinateSample_cast (q : ℚ) (w : ℚ × ℚ) :
    (rationalOrdinateSample q w : ℝ) =
      2 * (Analysis.rationalComplexCast w / (((1 / 2 : ℝ) : ℂ) + Complex.I * (q : ℂ))).re := by
  simp only [rationalOrdinateSample, Rat.cast_div, Rat.cast_mul, Rat.cast_add, Rat.cast_pow,
    Rat.cast_ofNat, Complex.div_re, Analysis.rationalComplexCast, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.ratCast_re, Complex.ratCast_im, zero_mul, mul_zero, sub_zero, one_mul,
    zero_add, add_zero, Complex.normSq_apply]
  ring

/-- An error bound for a unit-phase approximation gives a bound for the
signed ordinate term at any strictly positive rational ordinate. -/
theorem ordinateTerm_rational_error (v : ℝ) (q : ℚ) (w : ℚ × ℚ) (ε : ℝ) (hq : (0 : ℝ) < q)
    (happrox : ‖Complex.exp (Complex.I * (v : ℂ) * (q : ℂ)) - Analysis.rationalComplexCast w‖ ≤ ε) :
    |ordinateTerm v (q : ℝ) - (rationalOrdinateSample q w : ℝ)| ≤ 2 * ε / (q : ℝ) := by
  let d : ℂ := ((1 / 2 : ℝ) : ℂ) + Complex.I * (q : ℂ)
  have hden : (q : ℝ) ≤ ‖d‖ := by
    have h := Complex.abs_im_le_norm d
    have hi : d.im = (q : ℝ) := by
      simp only [d, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
        Complex.ratCast_re, Complex.I_im, Complex.ratCast_im, zero_mul, one_mul, zero_add]
    rw [hi, abs_of_pos hq] at h
    exact h
  have heps : 0 ≤ ε := (norm_nonneg _).trans happrox
  have hb := div_le_div₀ heps happrox hq hden
  have hc :=
    Complex.abs_re_le_norm
      ((Complex.exp (Complex.I * (v : ℂ) * (q : ℂ)) - Analysis.rationalComplexCast w) / d)
  rw [norm_div] at hc
  have hdiff :
    ordinateTerm v (q : ℝ) - (rationalOrdinateSample q w : ℝ) =
      2 *
        (((Complex.exp (Complex.I * (v : ℂ) * (q : ℂ)) - Analysis.rationalComplexCast w) /
            d).re) := by
    rw [rationalOrdinateSample_cast]
    simp only [ordinateTerm, ordinatePhase, Complex.ofReal_ratCast, sub_div, Complex.sub_re]
    ring
  rw [hdiff, abs_mul, abs_of_nonneg (by norm_num only : (0 : ℝ) ≤ 2)]
  have hm := mul_le_mul_of_nonneg_left (hc.trans hb) (by norm_num only : (0 : ℝ) ≤ 2)
  simpa only [mul_div_assoc] using hm

/-- The rounded rational phase evaluator bounds a real signed zero term
at rational phase and ordinate inputs, with an explicit rational error. -/
theorem ordinateTerm_scaled_error (v q : ℚ) (hq : (0 : ℝ) < q) {G n k : ℕ} (hG : 0 < G)
    (hv : |(((v * q) / (2 : ℚ) ^ k : ℚ) : ℝ)| / (n + 1 : ℕ) ≤ 1 / 2)
    (hrem : |(((v * q) / (2 : ℚ) ^ k : ℚ) : ℝ)| ^ n / (n.factorial : ℝ) * 2 ≤ 1 / (G : ℝ))
    (hsmall : ∀ j < k, (Analysis.roundedSquareBudget G j : ℝ) ≤ 1) :
    |ordinateTerm (v : ℝ) (q : ℝ) -
          (rationalOrdinateSample q (Analysis.rationalScaledPhase G (v * q) n k) : ℝ)| ≤
      ((2 * Analysis.roundedSquareBudget G k / q : ℚ) : ℝ) := by
  have h := Analysis.norm_scaled_phase_error hG (v * q) n k hv hrem hsmall
  have he :
    ‖Complex.exp (Complex.I * ((v : ℝ) : ℂ) * (q : ℂ)) -
          Analysis.rationalComplexCast (Analysis.rationalScaledPhase G (v * q) n k)‖ ≤
      (Analysis.roundedSquareBudget G k : ℝ) := by
    convert h using 1
    congr 2
    simp only [Rat.cast_mul, Complex.ofReal_ratCast, mul_assoc]
  have hm :=
    ordinateTerm_rational_error (v : ℝ) q (Analysis.rationalScaledPhase G (v * q) n k)
      (Analysis.roundedSquareBudget G k : ℝ) hq he
  simpa only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat] using hm

/-- Decide whether the rational ordinate sample and its rounded-phase error
lie between the rational endpoints lo and hi. -/
def rationalOrdinateNodeCheck (v q lo hi : ℚ) (G n k : ℕ) : Bool :=
  let z := rationalOrdinateSample q (Analysis.rationalScaledPhase G (v * q) n k)
  let e := 2 * Analysis.roundedSquareBudget G k / q
  decide (lo ≤ z - e ∧ z + e ≤ hi)

/-- A successful rational node check bounds the corresponding real zero
term, provided the evaluator's Taylor and rounding hypotheses hold. -/
theorem rationalOrdinateNodeCheck_sound (v q lo hi : ℚ) {G n k : ℕ} (hG : 0 < G) (hq : (0 : ℝ) < q)
    (hv : |(((v * q) / (2 : ℚ) ^ k : ℚ) : ℝ)| / (n + 1 : ℕ) ≤ 1 / 2)
    (hrem : |(((v * q) / (2 : ℚ) ^ k : ℚ) : ℝ)| ^ n / (n.factorial : ℝ) * 2 ≤ 1 / (G : ℝ))
    (hsmall : ∀ j < k, (Analysis.roundedSquareBudget G j : ℝ) ≤ 1)
    (hcheck : rationalOrdinateNodeCheck v q lo hi G n k = true) :
    (lo : ℝ) ≤ ordinateTerm (v : ℝ) (q : ℝ) ∧ ordinateTerm (v : ℝ) (q : ℝ) ≤ (hi : ℝ) := by
  have hc := of_decide_eq_true hcheck
  change
    lo ≤
        rationalOrdinateSample q (Analysis.rationalScaledPhase G (v * q) n k) -
          2 * Analysis.roundedSquareBudget G k / q ∧
      rationalOrdinateSample q (Analysis.rationalScaledPhase G (v * q) n k) +
          2 * Analysis.roundedSquareBudget G k / q ≤
        hi at hc
  have h1 :
    (lo : ℝ) ≤
      (rationalOrdinateSample q (Analysis.rationalScaledPhase G (v * q) n k) : ℝ) -
        ((2 * Analysis.roundedSquareBudget G k / q : ℚ) : ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr hc.1
    simpa only [Rat.cast_sub] using h
  have h2 :
    (rationalOrdinateSample q (Analysis.rationalScaledPhase G (v * q) n k) : ℝ) +
        ((2 * Analysis.roundedSquareBudget G k / q : ℚ) : ℝ) ≤
      (hi : ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr hc.2
    simpa only [Rat.cast_add] using h
  have he := abs_le.mp (ordinateTerm_scaled_error v q hq hG hv hrem hsmall)
  constructor <;> linarith only [h1, h2, he.1, he.2]

/-- For rational log heights of magnitude at most 21 and positive ordinates
at most 100, the fixed grid, Taylor length, and twelve squarings satisfy the
analytic hypotheses of the rational node checker. -/
theorem rationalOrdinateNodeCheck_100 (v q lo hi : ℚ) (hq : (0 : ℝ) < q) (hqu : (q : ℝ) ≤ 100)
    (hv : |(v : ℝ)| ≤ 21) (hcheck : rationalOrdinateNodeCheck v q lo hi (10 ^ 12) 16 12 = true) :
    (lo : ℝ) ≤ ordinateTerm (v : ℝ) (q : ℝ) ∧ ordinateTerm (v : ℝ) (q : ℝ) ≤ (hi : ℝ) := by
  have hp : |((v * q : ℚ) : ℝ)| ≤ 2100 := by
    rw [Rat.cast_mul, abs_mul, abs_of_pos hq]
    have h := mul_le_mul hv hqu hq.le (by norm_num only : (0 : ℝ) ≤ 21)
    norm_num only at h
    exact h
  have hred : |(((v * q) / (2 : ℚ) ^ 12 : ℚ) : ℝ)| ≤ 3 / 5 := by
    norm_num only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, abs_div, abs_of_pos] at ⊢
    linarith only [hp]
  have hpow := pow_le_pow_left₀ (abs_nonneg (((v * q) / (2 : ℚ) ^ 12 : ℚ) : ℝ)) hred 16
  apply
    rationalOrdinateNodeCheck_sound v q lo hi (G := 10 ^ 12) (n := 16) (k := 12)
      (by norm_num only : 0 < 10 ^ 12) hq
  · norm_num only
    linarith only [hred]
  · norm_num only [Nat.factorial] at hpow ⊢
    nlinarith only [hpow]
  · intro j hj
    interval_cases j <;>
      norm_num only [Analysis.roundedSquareBudget, Rat.cast_div, Rat.cast_sub, Rat.cast_mul,
        Rat.cast_pow, Rat.cast_ofNat, Rat.cast_natCast]
  · exact hcheck

/-- The first rational ordinate sample at log height 13.81 lies between
`0.06077` and `0.06079`. The node check is reduced by the kernel. -/
theorem ordinate_sample_first :
    (6077 / 100000 : ℝ) ≤ ordinateTerm (1381 / 100) (14473 / 1024) ∧
      ordinateTerm (1381 / 100) (14473 / 1024) ≤ (6079 / 100000 : ℝ) := by
  have h :=
    rationalOrdinateNodeCheck_100 (1381 / 100) (14473 / 1024) (6077 / 100000) (6079 / 100000)
      (by norm_num only) (by norm_num only) (by norm_num only) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
