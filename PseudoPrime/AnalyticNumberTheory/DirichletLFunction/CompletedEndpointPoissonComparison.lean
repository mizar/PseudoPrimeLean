/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PoissonZeroSum
public import PseudoPrime.Analysis.PoissonHorizontalComparison
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PositiveEulerPrefix

/-! # Endpoint Poisson comparisons retaining positive Euler prime-power prefixes -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- Under individual RH, primitive nonprincipal data at modulus at least two with
nonprincipal inverse and nonnegative shift h, the centered completed derivative at 1
is at most 1+2h times its centered value at 1+h. Compare positive Poisson kernels
termwise on the critical line and sum using nonnegative multiplicities.
This transfers endpoint estimates to an absolutely convergent Euler half-plane. -/
theorem completedLogDeriv_endpoint_le_shifted {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {h : ℝ} (hh : 0 ≤ h) :
    (logDeriv χ.completedLFunction 1).re + Real.log q / 2 ≤
      (1 + 2 * h) * ((logDeriv χ.completedLFunction ((1 + h : ℝ) : ℂ)).re + Real.log q / 2) := by
  let P := fun (σ : ℝ) (ρ : ℂ) ↦
    (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
      ((σ - 1 / 2) / Complex.normSq ((σ : ℂ) - ρ))
  have hs (σ : ℝ) (hσ : 1 / 2 < σ) : Summable (P σ) := by
    simpa only [P, Complex.ofReal_re] using
      summable_completed_poisson_terms hq hRH hp hne hinv (s := (σ : ℂ)) hσ
  have he (σ : ℝ) (hσ : 1 / 2 < σ) :
    (∑' ρ : ℂ, P σ ρ) = (logDeriv χ.completedLFunction (σ : ℂ)).re + Real.log q / 2 := by
    simpa only [P, Complex.ofReal_re] using
      completed_poissonSum_eq_logDeriv_re hq hRH hp hne hinv (s := (σ : ℂ)) hσ
  have ha : AnalyticOnNhd ℂ χ.completedLFunction Set.univ := fun z _ ↦
    (DirichletCharacter.differentiable_completedLFunction hne).analyticAt z
  have hm (ρ : ℂ) : (0 : ℝ) ≤ MeromorphicOn.divisor χ.completedLFunction Set.univ ρ := by
    exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg ha ρ
  have hterm (ρ : ℂ) : P 1 ρ ≤ (1 + 2 * h) * P (1 + h) ρ := by
    by_cases hD : MeromorphicOn.divisor χ.completedLFunction Set.univ ρ = 0
    · simp only [P, hD, Int.cast_zero, zero_mul, mul_zero, le_refl]
    · have hr :=
        completedLFunction_zero_re_eq_half_of_dirichletRH hRH hp hinv
          (dirichletCompletedLFunction_zero_of_divisor_univ_ne_zero hne hD)
      have hn (σ : ℝ) : Complex.normSq ((σ : ℂ) - ρ) = (σ - 1 / 2) ^ 2 + ρ.im ^ 2 := by
        rw [Complex.normSq_apply]
        simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, hr]
        ring
      have hk :=
        Analysis.poisson_horizontal_kernel_le_scaled (a := (1 / 2 : ℝ)) (b := 1 / 2 + h) (t := ρ.im)
          (by norm_num only) (by linarith only [hh])
      have hf : (1 / 2 + h : ℝ) / (1 / 2) = 1 + 2 * h := by ring
      rw [hf] at hk
      dsimp only [P]
      rw [hn, hn]
      have h1 : (1 : ℝ) - 1 / 2 = 1 / 2 := by ring
      have h2 : (1 + h : ℝ) - 1 / 2 = 1 / 2 + h := by ring
      rw [h1, h2]
      exact (mul_le_mul_of_nonneg_left hk (hm ρ)).trans_eq (by ring)
  have hb : 1 / 2 < (1 : ℝ) + h := by linarith only [hh]
  have ht :=
    Summable.tsum_le_tsum hterm (hs 1 (by norm_num only)) ((hs (1 + h) hb).mul_left (1 + 2 * h))
  rw [tsum_mul_left, he 1 (by norm_num only), he (1 + h) hb] at ht
  simpa only [Complex.ofReal_one] using ht

/-- Under primitive nonprincipal individual-RH data, positive shift r, Euler cap M,
Gamma upper bound G and any finite index set B, the real completed derivative at 1
is at most r*log(q)+(1+2r)*(G+M-positiveEulerPrefix(B,1+r)).
Apply horizontal Poisson comparison and the nonnegative Euler-series prefix bound.
This preserves arithmetic savings in first-pole residue estimates. -/
theorem completedLogDeriv_endpoint_le_positive_prefix {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {r M G : ℝ} (hr : 0 < r) (B : Finset ℕ)
    (hM : (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 + r)) ≤ M)
    (hG : (logDeriv χ.gammaFactor ((1 + r : ℝ) : ℂ)).re ≤ G) :
    (logDeriv χ.completedLFunction 1).re ≤
      r * Real.log q +
        (1 + 2 * r) *
          (G + M -
            ∑ n ∈ B, (1 + (χ n).re) * ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 + r)) := by
  have hcmp := completedLogDeriv_endpoint_le_shifted hq hRH hp hne hinv hr.le
  have hσ : 1 < 1 + r := by linarith only [hr]
  have hs : 1 ≤ (((1 + r : ℝ) : ℂ)).re := by
    rw [Complex.ofReal_re]; linarith only [hr]
  have hs0 := zero_lt_one.trans_le hs
  have hd :=
    logDeriv_dirichletLFunction_eq_completed_sub_gammaFactor_of_regular hne
      (completedLFunction_ne_zero_of_one_le_re hne hs) (gammaFactor_ne_zero_of_re_pos χ hs0)
      (analyticAt_gammaFactor_of_re_pos χ hs0).differentiableAt
  have he :
    (logDeriv χ.completedLFunction ((1 + r : ℝ) : ℂ)).re =
      (logDeriv χ.LFunction ((1 + r : ℝ) : ℂ)).re +
        (logDeriv χ.gammaFactor ((1 + r : ℝ) : ℂ)).re := by
    rw [hd, Complex.sub_re]
    ring
  have hpref := re_logDeriv_le_principal_sub_positive_prefix χ hσ B
  have hcap :
    (logDeriv χ.completedLFunction ((1 + r : ℝ) : ℂ)).re ≤
      G + M - ∑ n ∈ B, (1 + (χ n).re) * ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 + r) := by
    rw [he]
    linarith only [hpref, hM, hG]
  have hmul := mul_le_mul_of_nonneg_left hcap (show 0 ≤ 1 + 2 * r by linarith only [hr])
  nlinarith only [hcmp, hmul]

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
