/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028FiniteFirst
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028FiniteMomentCell

/-! # First finite-cell numerical budget -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The logarithm, negative power, and square root at the first cutoff have
the displayed rational bounds. The logarithm and power use kernel-checked
certificates, and the square-root bounds follow by squaring. -/
theorem target028_first_budget_inputs :
    Real.log 252 ≤ (553 / 100 : ℝ) ∧
      (252 : ℝ) ^ (-(27 / 25 : ℝ)) ≤ 255 / 100000 ∧
      (15874 / 1000 : ℝ) ≤ Real.sqrt 252 ∧ Real.sqrt 252 ≤ (15875 / 1000 : ℝ) := by
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 252 8 32 5 (553 / 100) = true from by
          decide +kernel)).2
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
        (show
          AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 252 0 (255 / 100000) 27 25 =
            true
          from by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl hp
  norm_num only at hp ⊢
  exact
    ⟨hl, hp, Real.le_sqrt_of_sq_le (by norm_num only),
      Real.sqrt_le_iff.mpr ⟨by norm_num only, by norm_num only⟩⟩

/-- The six-moment budget at cutoff 252 and logarithmic endpoint `30461/1000` is
at most `79/5`. Rational enclosures for the analytic inputs leave a strict
margin below the certified finite principal sum. -/
theorem target028_first_budget : target028MomentBudget 252 (30461 / 1000) ≤ (79 / 5 : ℝ) := by
  let z : ℝ := (21 / 8 : ℝ) + Real.log 252
  let Z : ℝ := (21 / 8 : ℝ) + 553 / 100
  let E : ℝ := Real.exp (-((27 / 25 : ℝ) * (21 / 8)))
  let P : ℝ := (252 : ℝ) ^ (-(27 / 25 : ℝ))
  let R : ℝ := Real.sqrt 252
  let F : ℝ := (refinedSixPoleKernel.function (1 / 2)).re
  have hl := target028_first_budget_inputs.1
  have hp := target028_first_budget_inputs.2.1
  have hr := target028_first_budget_inputs.2.2.1
  have hr' := target028_first_budget_inputs.2.2.2
  have hz0 : 0 ≤ z := by
    dsimp only [z]
    have h := Real.log_nonneg (by norm_num only : (1 : ℝ) ≤ 252)
    linarith only [h]
  have hz : z ≤ Z := by
    dsimp only [z, Z]; linarith only [hl]
  have he : E ≤ (588 / 10000 : ℝ) := by
    dsimp only [E]
    convert refined_exp_neg_unit_le using 1
    norm_num only
  have hp0 : 0 ≤ P := Real.rpow_nonneg (by norm_num only) _
  have hp' : P ≤ (255 / 100000 : ℝ) := hp
  have hf0 : 0 ≤ F := by
    dsimp only [F]
    rw [refined_six_pole_half]
    positivity
  have hf : F ≤ (35091 / 100000 : ℝ) := refined_six_pole_half_upper
  have hep := mul_le_mul he hp' hp0 (by norm_num only : (0 : ℝ) ≤ 588 / 10000)
  have hep0 : 0 ≤ (588 / 10000 : ℝ) * (255 / 100000) := by norm_num only
  have hpow := pow_le_pow_left₀ hz0 hz 5
  have hepz := mul_le_mul hep hpow (pow_nonneg hz0 5) hep0
  have hpoly0 : 0 ≤ target028MomentPolynomial z := by
    dsimp only [target028MomentPolynomial]
    positivity
  have hpoly := target028_moment_polynomial_le hz0 hz
  have hpolyZ : target028MomentPolynomial Z ≤ (1056940 : ℝ) := by
    dsimp only [Z, target028MomentPolynomial]
    norm_num only
  have hepoly := mul_le_mul hep (hpoly.trans hpolyZ) hpoly0 hep0
  have hRF := mul_le_mul hr' hf hf0 (by norm_num only : (0 : ℝ) ≤ 15875 / 1000)
  change R * F ≤ (15875 / 1000 : ℝ) * (35091 / 100000) at hRF
  have hinv : R⁻¹ ≤ (15874 / 1000 : ℝ)⁻¹ := by
    simpa only [one_div] using
      one_div_le_one_div_of_le (by norm_num only : (0 : ℝ) < 15874 / 1000) hr
  have hlinear : (1839 / 1000 : ℝ) * z + 2 ≤ (1839 / 1000 : ℝ) * Z + 2 := by
    simpa only [add_comm] using
      add_le_add_right (mul_le_mul_of_nonneg_left hz (by norm_num only : (0 : ℝ) ≤ 1839 / 1000)) 2
  have hinv0 : 0 ≤ R⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hlinearZ0 : 0 ≤ (1839 / 1000 : ℝ) * Z + 2 := by
    dsimp only [Z]; norm_num only
  have herr := mul_le_mul hlinear hinv hinv0 hlinearZ0
  dsimp only [target028MomentBudget, target028ReflectedMomentUpper]
  rw [add_comm (Real.log 252) (21 / 8 : ℝ)]
  change
    (2 * (30461 / 1000 : ℝ)) * (((27 / 25 : ℝ) ^ 5 / 120) * E * P * z ^ 5) +
            (39 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 2 +
            (((27 / 25 : ℝ) ^ 5 / 120) * E * P) * target028MomentPolynomial z +
            (3 / 8 : ℝ) * (30461 / 1000 : ℝ) -
          (547 / 100 : ℝ) * (27 / 25 : ℝ) ^ 5 +
        R * F +
        ((231 / 5000 : ℝ) * ((203 / 1000) * (27 / 25 : ℝ) ^ 5) +
          ((1839 / 1000 : ℝ) * z + 2) * ((251 / 500 : ℝ) * (27 / 25 : ℝ) ^ 5) / R) ≤
      _
  dsimp only [Z] at hepz herr
  simp only [div_eq_mul_inv] at herr ⊢
  norm_num only at hepz hepoly hRF herr ⊢
  nlinarith only [hepz, hepoly, hRF, herr]

/-- A uniform Korselt product of three odd primes has a 0.28 rejecting prime
when its logarithm lies between 30 and `30461/1000`. The fixed cutoff 252 fits the
lower endpoint, and the certified principal prefix exceeds the cell budget. -/
theorem target028_first_pair_witness {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hsq : Squarefree n) (hnprod : n = p * q * r)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 1 < n) (ho : Odd n)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n) (hrn : r ∣ n)
    (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1)) (hL : (30 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 30461 / 1000) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (252 : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 := by nlinarith only [hL]
  have hS :
    (79 / 20 : ℝ) ≤
      ∑ k ∈ Finset.Ioc 0 ⌊(252 : ℝ)⌋₊,
        (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) 252 k).re :=
    le_of_lt target028_first_principal_lower
  have hcert : target028MomentBudget 252 (30461 / 1000) ≤ 4 * (79 / 20 : ℝ) := by
    norm_num only
    exact target028_first_budget
  exact
    target028_finite_moment_of_partial hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK
      hqK hrK hvq hvr (X := 252) (U := 30461 / 1000) (S := 79 / 20) (by norm_num only) hU hcut hS
      hcert

end PseudoPrime.PrimeTestBounds.MillerRabin
