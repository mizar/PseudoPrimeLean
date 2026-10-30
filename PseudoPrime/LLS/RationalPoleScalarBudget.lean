/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.RationalPoleFiniteJacobi
public import PseudoPrime.LLS.RationalPoleCertificates
public import PseudoPrime.NumberTheory.MarkedPrimeFactorLogMean
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.TwoPoleGammaZeroMass
/-! # Scalar local and Euler budgets for the fourth-pole finite criterion -/

public section

namespace PseudoPrime.LLS.PaperStatements
/-- The actual scaled weight is nonnegative at every positive scale and argument. -/
theorem fourScaledWeight_nonneg {x t : ℝ} (hx : 0 < x) (ht : 0 < t) :
    0 ≤ fourScaledWeight x t := by
  dsimp only [fourScaledWeight, fourPoleKernelWeight]
  exact div_nonneg
    (div_nonneg (rationalPoleFourKernel.mellin_nonneg _ (div_pos ht hx))
      (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)

/-- At a prime and positive exponent, the quadratic local discrepancy is bounded
by `(20/sqrt x) log p`, uniformly in the exponent and character value. -/
theorem fourPoleLocalTerm_prime_power_le {q p k : ℕ} (χ : DirichletCharacter ℂ q)
    (hquad : χ.IsQuadratic)
    {x : ℝ} (hx : 0 < x) (hp : p.Prime) (hk : 0 < k) :
    fourPoleLocalTerm χ x (p ^ k) ≤ (20 / Real.sqrt x) * Real.log p := by
  have hpR : 0 < (p ^ k : ℕ) := pow_pos hp.pos _
  have hw := fourScaledWeight_nonneg hx (Nat.cast_pos.mpr hpR)
  have hb := (le_abs_self (fourScaledWeight x (p ^ k : ℕ))).trans
    (fourScaledWeight_global_bound hx (Nat.cast_pos.mpr hpR))
  have hlog : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  have hc : 1 - (χ (p ^ k : ℕ)).re ≤ 2 := by
    rcases hquad (p ^ k : ℕ) with h | h | h
    · rw [h, Complex.zero_re]
      norm_num only
    · rw [h, Complex.one_re]
      norm_num only
    · rw [h, Complex.neg_re, Complex.one_re]
      norm_num only
  rw [fourPoleLocalTerm, ArithmeticFunction.vonMangoldt_apply_pow hk.ne',
    ArithmeticFunction.vonMangoldt_apply_prime hp]
  calc
    _ ≤ 2 * (Real.log p * fourScaledWeight x (p ^ k : ℕ)) := by
      nlinarith only [mul_le_mul_of_nonneg_right hc (mul_nonneg hlog hw)]
    _ ≤ 2 * (Real.log p * (10 / Real.sqrt x)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb hlog) (by norm_num only)
    _ = _ := by ring

/-- For positive ambient modulus and scale at least two, the exact quadratic local
cost is bounded by `(20/sqrt x)(log x/log 2)log a`.
Reindex by prime powers, enlarge each prime set to the ambient prime factors,
and bound the exponent count and prime-factor logarithmic sum. -/
theorem fourPoleLocalCost_le_log {q a : ℕ} (χ : DirichletCharacter ℂ q) (hquad : χ.IsQuadratic)
    (ha : 0 < a) {x : ℝ} (hx : 2 ≤ x) :
    fourPoleLocalCost χ a x ≤
      (20 / Real.sqrt x) * (Real.log x / Real.log 2) * Real.log a := by
  have hx0 : 0 < x := (by norm_num only : (0 : ℝ) < 2).trans_le hx
  have hC : 0 ≤ 20 / Real.sqrt x := div_nonneg (by norm_num only) (Real.sqrt_nonneg x)
  have hlogA : 0 ≤ Real.log a := Real.log_natCast_nonneg a
  have hK : 0 ≤ Real.log x / Real.log 2 :=
    div_nonneg (Real.log_nonneg ((by norm_num only : (1 : ℝ) ≤ 2).trans hx))
      (Real.log_nonneg (by norm_num only))
  rw [fourPoleLocalCost_prime_powers χ a hx0.le]
  have hprime (k : ℕ) (hk : k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊) :
      (∑ p ∈ (Finset.Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊).filter
        (fun p ↦ p.Prime ∧ p ∣ a), fourPoleLocalTerm χ x (p ^ k)) ≤
      (20 / Real.sqrt x) * Real.log a := by
    have hk0 : 0 < k := (Finset.mem_Icc.mp hk).1
    calc
      _ ≤ ∑ p ∈ (Finset.Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊).filter
          (fun p ↦ p.Prime ∧ p ∣ a), (20 / Real.sqrt x) * Real.log p :=
        Finset.sum_le_sum (fun p hp ↦
          fourPoleLocalTerm_prime_power_le χ hquad hx0 (Finset.mem_filter.mp hp).2.1 hk0)
      _ ≤ ∑ p ∈ a.primeFactors, (20 / Real.sqrt x) * Real.log p := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          have h := (Finset.mem_filter.mp hp).2
          exact Nat.mem_primeFactors.mpr ⟨h.1, h.2, ha.ne'⟩
        · intro p _ _
          exact mul_nonneg hC (Real.log_natCast_nonneg p)
      _ = (20 / Real.sqrt x) * ∑ p ∈ a.primeFactors, Real.log p :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (NumberTheory.sum_log_primeFactors_le_log ha) hC
  have hsum := Finset.sum_le_sum hprime
  rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul] at hsum
  have hfloor := Nat.floor_le hK
  calc
    _ ≤ (⌊Real.log x / Real.log 2⌋₊ : ℝ) *
        ((20 / Real.sqrt x) * Real.log a) := hsum
    _ ≤ (Real.log x / Real.log 2) * ((20 / Real.sqrt x) * Real.log a) :=
      mul_le_mul_of_nonneg_right hfloor (mul_nonneg hC hlogA)
    _ = _ := by ring

/-- On the real interval `[1,2]`, every Gamma factor has absolute real logarithmic
derivative at most two, using the existing common prefix allowance. -/
theorem fourPole_gammaFactor_le_two {q : ℕ} (χ : DirichletCharacter ℂ q) {σ : ℝ}
    (hl : 1 ≤ σ) (hu : σ ≤ 2) : |(logDeriv χ.gammaFactor (σ : ℂ)).re| ≤ 2 := by
  have h := AnalyticNumberTheory.DirichletLFunction.abs_re_logDeriv_gammaFactor_le_prefix χ
    hl (hu.trans (by norm_num only)) (R := 1 / 2) le_rfl (by linarith only [hl]) 0
  norm_num only [AnalyticNumberTheory.Gamma.gammaPrefixAllowance, Finset.sum_range_zero,
    sub_zero, max_def, ite_true] at h
  exact h.trans (by norm_num only)

/-- On the real interval `[13/9,2]`, the principal Euler logarithmic derivative
has absolute real part at most nine, by the four-over-gap Euler bound. -/
theorem fourPole_principalEuler_le_nine {σ : ℝ} (hl : 13 / 9 ≤ σ) (hu : σ ≤ 2) :
    |(logDeriv (1 : DirichletCharacter ℂ 1).LFunction (σ : ℂ)).re| ≤ 9 := by
  have hp : 0 < σ - 1 := by linarith only [hl]
  have h := AnalyticNumberTheory.DirichletLFunction.norm_logDeriv_vertical_le_four_div_gap
    (1 : DirichletCharacter ℂ 1) hp (by linarith only [hu]) 0
  simp only [Complex.ofReal_zero, zero_mul, add_zero,
    show 1 + (σ - 1) = σ by ring] at h
  apply ((Complex.abs_re_le_norm _).trans h).trans
  apply (div_le_iff₀ hp).mpr
  linarith only [hl]

/-- The empty-prefix fourth-pole Euler budget is at most `(2501/10000)log q+1000`.
Keep the exact two-node conductor coefficient and bound the remaining Gamma
and principal Euler terms by elementary fixed-interval estimates. -/
theorem fourPole_emptyEulerBudget_le {q : ℕ} (χ : DirichletCharacter ℂ q) :
    rationalPoleFourEulerBudget χ ∅ ∅ ≤ (2501 / 10000 : ℝ) * Real.log q + 1000 := by
  have hga := fourPole_gammaFactor_le_two χ
    (σ := 1 / 2 + poleFourAlpha) (by norm_num only [poleFourAlpha])
    (by norm_num only [poleFourAlpha])
  have hgb := fourPole_gammaFactor_le_two χ
    (σ := 1 / 2 + poleFourBeta) (by norm_num only [poleFourBeta])
    (by norm_num only [poleFourBeta])
  have hza := fourPole_principalEuler_le_nine
    (σ := 1 / 2 + poleFourAlpha) (by norm_num only [poleFourAlpha])
    (by norm_num only [poleFourAlpha])
  have hzb := fourPole_principalEuler_le_nine
    (σ := 1 / 2 + poleFourBeta) (by norm_num only [poleFourBeta])
    (by norm_num only [poleFourBeta])
  have hU : 0 ≤ poleFourUpperWeight - poleFourLowerWeight := by
    norm_num only [poleFourUpperWeight, poleFourLowerWeight,
      poleFourAlpha, poleFourBeta]
  have hL : 0 ≤ poleFourLowerWeight := by
    norm_num only [poleFourLowerWeight, poleFourAlpha, poleFourBeta]
  have hmain : (poleFourUpperWeight - poleFourLowerWeight) / 2 ≤
      (2501 / 10000 : ℝ) := by
    norm_num only [poleFourUpperWeight, poleFourLowerWeight,
      poleFourAlpha, poleFourBeta]
  have hconst : (poleFourUpperWeight - poleFourLowerWeight) * 11 +
      poleFourLowerWeight * 22 ≤ (1000 : ℝ) := by
    norm_num only [poleFourUpperWeight, poleFourLowerWeight,
      poleFourAlpha, poleFourBeta]
  dsimp only [rationalPoleFourEulerBudget]
  simp only [Finset.sum_empty, sub_zero]
  have h1 := mul_le_mul_of_nonneg_left
    (show (Real.log q / 2 +
      (logDeriv χ.gammaFactor ((1 / 2 + poleFourAlpha : ℝ) : ℂ)).re -
      (logDeriv (1 : DirichletCharacter ℂ 1).LFunction
        ((1 / 2 + poleFourAlpha : ℝ) : ℂ)).re) ≤ Real.log q / 2 + 11 by
      linarith only [(abs_le.mp hga).2, (abs_le.mp hza).1]) hU
  have h2 := mul_le_mul_of_nonneg_left
    (show ((logDeriv χ.gammaFactor ((1 / 2 + poleFourAlpha : ℝ) : ℂ)).re -
      (logDeriv χ.gammaFactor ((1 / 2 + poleFourBeta : ℝ) : ℂ)).re +
      (logDeriv (1 : DirichletCharacter ℂ 1).LFunction
        ((1 / 2 + poleFourBeta : ℝ) : ℂ)).re -
      (logDeriv (1 : DirichletCharacter ℂ 1).LFunction
        ((1 / 2 + poleFourAlpha : ℝ) : ℂ)).re) ≤ 22 by
      linarith only [(abs_le.mp hga).2, (abs_le.mp hgb).1,
        (abs_le.mp hzb).2, (abs_le.mp hza).1]) hL
  have hm := mul_le_mul_of_nonneg_right hmain (Real.log_natCast_nonneg q)
  nlinarith only [h1, h2, hm, hconst]
/-- Under GRH, a strict scalar inequality with conductor logarithm, arithmetic error,
and ambient logarithmic local-cost cap produces a negative Jacobi odd-prime witness.
Use the empty Euler prefixes and insert both proved scalar budget bounds. -/
theorem fourPole_exists_jacobi_scalar {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {x : ℝ} (hx : 2 ≤ x)
    (hgap : (2501 / 10000 : ℝ) *
        Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor + 1003 +
        (24 * Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor + 793) *
          x ^ (-3 / 4 : ℝ) +
        (65 * x ^ (1 / 4 : ℝ) + 120 / Real.sqrt x) +
          (20 / Real.sqrt x) * (Real.log x / Real.log 2) * Real.log (4 * n) <
      Real.sqrt x *
        (2 * ((484820459 / 528581976 : ℝ) * Real.exp (-(14 / 13))) -
          (2 * (13 / 25 : ℝ) * Real.exp (14 / 25) / (1 + 13 / 25) ^ 4))) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ x ∧ jacobiSym n p = -1 := by
  apply fourPole_exists_jacobi_of_gap bridge hGRH hx ∅ ∅
  have he := fourPole_emptyEulerBudget_le bridge.character
  have hl := fourPoleLocalCost_le_log bridge.character bridge.character_quadratic
    (Nat.mul_pos (by norm_num only : (0 : ℕ) < 4) hn.pos) hx
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hl
  linarith only [he, hl, hgap]

/-- The exact principal gap exceeds `567/2000`, as a consequence of the existing
quadratic coefficient certificate and positivity of its principal gap. -/
theorem fourPole_principal_gap_gt :
    (567 / 2000 : ℝ) <
      2 * ((484820459 / 528581976 : ℝ) * Real.exp (-(14 / 13))) -
        (2 * (13 / 25 : ℝ) * Real.exp (14 / 25) / (1 + 13 / 25) ^ 4) := by
  have h := rationalPole_quadratic_certificate
  have he : (rationalPoleFourKernel.function (1 / 2)).re =
      2 * (13 / 25 : ℝ) * Real.exp (14 / 25) / (1 + 13 / 25) ^ 4 := by
    rw [rationalPoleFourKernel, rationalPole_half_value]
  have hm : rationalPoleFourKernel.mass = (1 / 4 : ℝ) :=
    rationalPole_four_mass (by norm_num only) (by norm_num only)
  rw [rationalPole_four_cutoff, he, hm] at h
  norm_num only at h
  by_contra hnot
  have hle := le_of_not_gt hnot
  norm_num only at hle
  have hs := mul_self_le_mul_self h.1.le hle
  nlinarith only [h.2, hs]

end PseudoPrime.LLS.PaperStatements
