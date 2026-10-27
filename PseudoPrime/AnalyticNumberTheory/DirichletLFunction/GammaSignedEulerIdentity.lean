/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaSignedPoissonIdentity
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.Basic

/-! # Exact real Euler identity for the signed Gamma Poisson comparison -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- At a real argument, each twisted Mangoldt L-series term has real part
equal to the real character value times the real Mangoldt power weight.
The zero term vanishes. Positive integer bases turn the complex power into
the real power; this supplies the termwise identity before the series map. -/
theorem re_twistedMangoldt_term {q : ℕ} (χ : DirichletCharacter ℂ q) (σ : ℝ) (n : ℕ) :
    (LSeries.term (fun k : ℕ ↦ χ k * (ArithmeticFunction.vonMangoldt k : ℂ)) (σ : ℂ) n).re =
      (χ n).re * ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ σ := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [LSeries.term_zero, Complex.zero_re, ArithmeticFunction.map_zero, mul_zero, zero_div]
  · rw [LSeries.term_of_ne_zero hn,
      show (n : ℂ) = ((n : ℝ) : ℂ) from (Complex.ofReal_natCast n).symm, ←
      Complex.ofReal_cpow (Nat.cast_nonneg n) σ, Complex.div_ofReal_re]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

/-- To the right of one, the ordinary logarithmic derivative has the exact
real twisted Mangoldt series with its negative sign. Absolute convergence
permits taking real parts term by term. This is the Euler-side identity needed
to combine the signed resolvent nodes before estimating their prefix. -/
theorem re_logDeriv_eq_signed_Mangoldt_tsum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {σ : ℝ}
    (hσ : 1 < σ) :
    (logDeriv χ.LFunction (σ : ℂ)).re =
      -(∑' n : ℕ, (χ n).re * ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ σ) := by
  have hs : 1 < (σ : ℂ).re := by simpa only [Complex.ofReal_re] using hσ
  have hi := DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hs
  have hI :
    Summable
      (fun n : ℕ ↦
        LSeries.term (fun k : ℕ ↦ χ k * (ArithmeticFunction.vonMangoldt k : ℂ)) (σ : ℂ) n) := by
    have hf :
      ((fun k : ℕ ↦ χ k) * (fun k : ℕ ↦ (ArithmeticFunction.vonMangoldt k : ℂ))) =
        (fun k : ℕ ↦ χ k * (ArithmeticFunction.vonMangoldt k : ℂ)) := by
      funext k
      exact Pi.mul_apply _ _ _
    rw [LSeriesSummable, hf] at hi
    exact hi
  have h :=
    congrArg Complex.re
      (lSeries_twist_vonMangoldt_eq_neg_logDeriv_dirichletLFunction_of_one_lt_re χ hs)
  unfold LSeries at h
  rw [Complex.re_tsum hI] at h
  simp only [neg_div, ← logDeriv_apply, Complex.neg_re, re_twistedMangoldt_term] at h
  linarith only [h]

/-- To the right of one, real character values preserve absolute convergence
of the Mangoldt power series. Their absolute values are at most one, so the
untwisted nonnegative Mangoldt series dominates the term norms. This supports
the finite signed-node interchange in the common Euler identity. -/
theorem summable_real_twistedMangoldt {q : ℕ} (χ : DirichletCharacter ℂ q) {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ ↦ (χ n).re * ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ σ) := by
  apply (Arithmetic.summable_vonMangoldt_div_rpow hσ).of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) σ)]
  have hχ := (Complex.abs_re_le_norm (χ n)).trans (χ.norm_le_one n)
  have hm := mul_le_mul_of_nonneg_right hχ (ArithmeticFunction.vonMangoldt_nonneg (n := n))
  simpa only [one_mul] using div_le_div_of_nonneg_right hm (Real.rpow_nonneg (Nat.cast_nonneg n) σ)

/-- The finite signed ordinary-derivative combination equals the single
character Euler series weighted by the actual common Gamma Mangoldt weight.
Absolute convergence permits interchanging the finite coefficient list and
the infinite series. Coefficient signs are retained before estimating prefixes. -/
theorem gammaResolvent_signed_ordinary_eq_euler {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    (Analysis.gammaResolventCoefficients.map
          (fun ab ↦ (ab.2 : ℝ) * (logDeriv χ.LFunction (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re)).sum =
      ∑' n : ℕ, -(χ n).re * Analysis.gammaResolventMangoldtWeight n := by
  let f := fun (ab : ℚ × ℚ) (n : ℕ) ↦
    (ab.2 : ℝ) *
      (-((χ n).re * ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ ((1 / 2 : ℝ) + (ab.1 : ℝ))))
  have hσ (ab : ℚ × ℚ) (hab : ab ∈ Analysis.gammaResolventCoefficients) :
    1 < (1 / 2 : ℝ) + (ab.1 : ℝ) := by
    have ha := List.forall_iff_forall_mem.mp Analysis.gammaResolvent_scales_gt_half ab hab
    have h : ((1 / 2 : ℚ) : ℝ) < (ab.1 : ℝ) := Rat.cast_lt.mpr ha
    norm_num only at h
    linarith only [h]
  have hs (ab : ℚ × ℚ) (hab : ab ∈ Analysis.gammaResolventCoefficients) : Summable (f ab) :=
    ((summable_real_twistedMangoldt χ (hσ ab hab)).neg).mul_left (ab.2 : ℝ)
  have he (n : ℕ) :
    -(χ n).re * Analysis.gammaResolventMangoldtWeight n =
      (Analysis.gammaResolventCoefficients.map (fun ab ↦ f ab n)).sum := by
    dsimp only [f, Analysis.gammaResolventMangoldtWeight, Analysis.gammaResolventEulerWeight]
    norm_num only [Analysis.gammaResolventCoefficients, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil]
    simp only [Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
    ring
  rw [tsum_congr he, Analysis.tsum_list_sum Analysis.gammaResolventCoefficients f hs]
  apply congrArg List.sum
  apply List.map_congr_left
  intro ab hab
  dsimp only [f]
  rw [← Complex.ofReal_add, re_logDeriv_eq_signed_Mangoldt_tsum χ (hσ ab hab), tsum_mul_left,
    tsum_neg]

/-- Under individual RH and primitive nonprincipal conductor data, the actual
Gamma resolvent zero mass equals its exact conductor contribution, signed
Gamma-node contribution and the common-weight Euler series. Both the Poisson
and Euler identities are discharged. This is the exact signed comparison
used before absorbing the local nonunit correction. -/
theorem gammaResolvent_zeroMass_eq_signed_euler {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    (∑' ρ : ℂ,
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
          Analysis.gammaResolventMajorant ρ.im) =
      (11783423 / 25000000 : ℝ) * Real.log q +
        (Analysis.gammaResolventCoefficients.map
            (fun ab ↦
              (ab.2 : ℝ) * (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re)).sum +
        ∑' n : ℕ, -(χ n).re * Analysis.gammaResolventMangoldtWeight n := by
  rw [gammaResolvent_zeroMass_eq_conductor_signed_derivatives hq hRH hp hne hinv,
    gammaResolvent_signed_ordinary_eq_euler χ]

/-- The actual Gamma zero mass obeys the signed prefix upper bound under
individual RH and primitive nonprincipal conductor data. The common Euler
weight gives twice the prefix gain, and its nonunit correction is retained
exactly. This is the zero-side interface for the joint local conductor budget. -/
theorem gammaResolvent_zeroMass_le_signed_prefix {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (B : Finset ℕ) :
    (∑' ρ : ℂ,
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
          Analysis.gammaResolventMajorant ρ.im) ≤
      (11783423 / 25000000 : ℝ) * Real.log q +
            (Analysis.gammaResolventCoefficients.map
                (fun ab ↦
                  (ab.2 : ℝ) * (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re)).sum +
            (∑' n : ℕ, Analysis.gammaResolventMangoldtWeight n) -
          2 * (∑ n ∈ B, Analysis.gammaResolventMangoldtWeight n) +
        ∑ n ∈ B, (1 - (χ n).re) * Analysis.gammaResolventMangoldtWeight n := by
  rw [gammaResolvent_zeroMass_eq_signed_euler hq hRH hp hne hinv]
  have h := Analysis.gamma_character_signed_euler_prefix_le χ B
  linarith only [h]

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
