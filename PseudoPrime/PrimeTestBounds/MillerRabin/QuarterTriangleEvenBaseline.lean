/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTriangleOriginIntegral
public import PseudoPrime.LLS.PaperStatements.TriangularSignedGammaBounds

/-! # Even character baseline for the wide triangle -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Reflection and duplication at one quarter evaluate the even character's
central digamma baseline in terms of Euler's constant, pi and log two. -/
theorem triangle_digamma_quarter :
    (Complex.digamma (1 / 4)).re =
      -Real.eulerMascheroniConstant - Real.pi / 2 - 3 * Real.log 2 := by
  have hi (n : ℤ) : (1 / 4 : ℂ) ≠ n := by
    intro he
    have hn : (1 / 4 : ℝ) = n := by
      apply Complex.ofReal_inj.mp
      push_cast
      exact he
    by_cases h : n ≤ 0
    · linarith only [hn, (show (n : ℝ) ≤ 0 by exact_mod_cast h)]
    · have h1 : 1 ≤ n := Int.add_one_le_iff.mpr (lt_of_not_ge h)
      linarith only [hn, (show (1 : ℝ) ≤ n by exact_mod_cast h1)]
  have hd :=
    Complex.digamma_two_mul (s := 1 / 4)
      (fun m he => by
        have h : (2 : ℝ) * (1 / 4) = -(m : ℝ) := by
          apply Complex.ofReal_inj.mp
          push_cast
          exact he
        linarith only [h, Nat.cast_nonneg (α := ℝ) m])
  have hr := Complex.digamma_one_sub hi
  have hc : Complex.cot ((Real.pi : ℂ) * (1 / 4)) = 1 := by
    rw [show (Real.pi : ℂ) * (1 / 4) = ((Real.pi / 4 : ℝ) : ℂ) by
        push_cast; ring,
      Complex.cot_eq_cos_div_sin, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_four,
      Real.sin_pi_div_four, div_self (by norm_num)]
  rw [hc, mul_one] at hr
  rw [show (2 : ℂ) * (1 / 4) = 1 / 2 by norm_num only, Complex.digamma_one_half,
    show (1 / 4 : ℂ) + 1 / 2 = 1 - 1 / 4 by ring, hr] at hd
  have he :
    Complex.digamma (1 / 4) =
      -(Real.eulerMascheroniConstant : ℂ) - (Real.pi : ℂ) / 2 - 3 * Complex.log 2 := by
    linear_combination -hd
  rw [he,
    show Complex.log 2 = ((Real.log 2 : ℝ) : ℂ) from
      (Complex.ofReal_log (by norm_num only : (0 : ℝ) ≤ 2)).symm]
  norm_num only [Complex.sub_re, Complex.neg_re, Complex.ofReal_re, Complex.div_ofNat_re,
    Complex.mul_re, Complex.ofReal_im, Complex.re_ofNat, mul_zero, sub_zero]

/-- Twice the real logarithmic derivative of the even gamma factor at the
central point is the explicit baseline in the wide-triangle origin integral. -/
theorem triangle_even_baseline {q : ℕ} {χ : DirichletCharacter ℂ q} (hχ : χ.Even) :
    2 * (logDeriv χ.gammaFactor (1 / 2)).re =
      -Real.eulerMascheroniConstant - Real.pi / 2 - 3 * Real.log 2 - Real.log Real.pi := by
  have hhalf : (1 / 2 : ℂ) / 2 = 1 / 4 := by norm_num only
  have hp : 0 < ((1 / 2 : ℂ) / 2).re := by
    rw [hhalf]
    norm_num only [Complex.div_ofNat_re, Complex.one_re]
  rw [AnalyticNumberTheory.DirichletLFunction.gammaLogDeriv_even_eq_digamma hχ
      (fun n => AnalyticNumberTheory.Gamma.not_neg_nat_of_re_pos hp n),
    hhalf, ← Complex.ofReal_log Real.pi_pos.le]
  simp only [Complex.add_re, Complex.div_ofNat_re, Complex.neg_re, Complex.ofReal_re,
    triangle_digamma_quarter]
  ring

/-- For an even character the central logarithmic derivative plus the actual
half-line correction equals the certified origin series constant. -/
theorem triangle_even_origin_eq {q : ℕ} {χ : DirichletCharacter ℂ q} (hχ : χ.Even) :
    2 * (logDeriv χ.gammaFactor (1 / 2)).re +
        2 *
          (∫ x in Set.Ioi (0 : ℝ),
            Real.exp (-x / 2) * min (x / (5 / 2)) 1 / (1 - Real.exp (-2 * x))) =
      triangleOriginGamma := by
  rw [triangle_even_baseline hχ, triangle_origin_integral_series, triangleOriginGamma]
  ring

end PseudoPrime.PrimeTestBounds.MillerRabin
