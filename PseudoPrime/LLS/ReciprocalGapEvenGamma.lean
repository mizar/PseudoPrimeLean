/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ReciprocalGapRationalGamma

/-! # Certified parity savings for reciprocal-gap Gamma inputs -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For an even character at any level and real r>0, its Gamma logarithmic
derivative has real part equal to the even scalar expression. Exclude poles by
positive real part and evaluate the exact even Gamma formula. This retains parity
when supplying the real-axis inputs to reciprocal-gap witness comparisons. -/
theorem reciprocalGapGamma_re_eq_even {q : ℕ} {χ : DirichletCharacter ℂ q} (he : χ.Even) {r : ℝ}
    (hr : 0 < r) : (logDeriv χ.gammaFactor (r : ℂ)).re = reciprocalGapEvenGammaLower r := by
  have hp : 0 < ((r : ℂ) / 2).re := by
    rw [complex_div_two_re, Complex.ofReal_re]
    linarith only [hr]
  rw [AnalyticNumberTheory.DirichletLFunction.logDeriv_gammaFactor_eq_of_even_of_half_ne_neg_nat he
      (fun n ↦ AnalyticNumberTheory.Gamma.not_neg_nat_of_re_pos hp n)]
  rw [← Complex.ofReal_log Real.pi_pos.le]
  unfold reciprocalGapEvenGammaLower
  simp only [Complex.add_re, Complex.div_ofNat_re, Complex.neg_re, Complex.ofReal_re,
    Complex.ofReal_div, Complex.ofReal_ofNat]
  ring

/-- The inverse of an even complex Dirichlet character is even, at any level.
Evaluate the inverse character at minus one. This supplies the parity premise for
the pole and reflected-real-axis estimates. -/
theorem reciprocalGap_inverse_even {q : ℕ} {χ : DirichletCharacter ℂ q} (he : χ.Even) :
    χ⁻¹.Even := by
  change χ⁻¹ (-1) = 1
  rw [MulChar.inv_apply_eq_inv', show χ (-1) = 1 from he, inv_one]

/-- At 127/100, the even Gamma scalar is at most -1281/1000.
Certify digamma(127/200) by rational finite sums and use the proved lower bound on
log pi. This improves the zero-comparison Gamma input for even characters. -/
theorem reciprocalGapEvenGamma_at_127_div_100 :
    reciprocalGapEvenGammaLower (127 / 100) ≤ -(1281 / 1000 : ℝ) := by
  have hd :=
    AnalyticNumberTheory.Gamma.rationalDigammaIntervalCheck_sound
      (show
        AnalyticNumberTheory.Gamma.rationalDigammaIntervalCheck (127 / 200) 32 6 24 (-142 / 100)
            (-1419 / 1000) =
          true
        by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] at hd
  unfold reciprocalGapEvenGammaLower
  norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat]
  linarith only [hd.2, Analysis.log_pi_ge_2096_div_1831]

/-- At 6/5, the even Gamma scalar is at most -1342/1000.
Certify digamma(3/5) by rational finite sums and bound log pi below.
This improves the pole-budget Gamma input for even characters. -/
theorem reciprocalGapEvenGamma_at_six_fifths :
    reciprocalGapEvenGammaLower (6 / 5) ≤ -(1342 / 1000 : ℝ) := by
  have hd :=
    AnalyticNumberTheory.Gamma.rationalDigammaIntervalCheck_sound
      (show
        AnalyticNumberTheory.Gamma.rationalDigammaIntervalCheck (3 / 5) 32 6 24 (-1541 / 1000)
            (-154 / 100) =
          true
        by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] at hd
  unfold reciprocalGapEvenGammaLower
  norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat]
  linarith only [hd.2, Analysis.log_pi_ge_2096_div_1831]

/-- At a nonzero original level, the primitive character of an even character is even.
Transfer the value at minus one, which is coprime to every level.
This preserves the parity saving after primitive normalization. -/
theorem reciprocalGap_primitiveCharacter_even {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (he : χ.Even) : χ.primitiveCharacter.Even := by
  change χ.primitiveCharacter (-1) = 1
  have hc : IsCoprime (-1 : ℤ) (N : ℤ) := (isCoprime_one_left).neg_left
  have hv := DirichletCharacter.primitiveCharacter_apply_of_isCoprime χ hc
  simp only [Int.cast_neg, Int.cast_one] at hv
  exact hv.trans he

end PseudoPrime.LLS.PaperStatements
