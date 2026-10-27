/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PairedEulerPrimeCosts
public import PseudoPrime.LLS.TwoPoleRetainedPrefixBounds

/-! # Parameterized allocation of conductor savings to Euler and local costs -/

@[expose] public section

namespace PseudoPrime.LLS

/-- For a nonprincipal quadratic character under GRH, let a and d be nonnegative scalar
prime-cost bounds. If (1/2-a) sqrt x is at least one, the local correction and unramified prefix
cost cancel against complementary portions of the conductor saving. Under unit-prime triviality,
the resulting arithmetic upper bound retains the full principal prefix minus d. The proof uses
the exact logarithmic conductor identity before enlarging to the ambient level. This allows
new scalar prime costs and smaller-scale local absorption without changing the witness proof. -/
theorem gamma_primitive_add_local_le_of_parameterized_conductor_prefix {q A : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hquad : χ.IsQuadratic) (hne : χ ≠ 1) (hqA : q ≤ A)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x C Y a d : ℝ} (hx : 2 ≤ x)
    (hY : 1 ≤ Y) (ha : 0 ≤ a) (hd0 : 0 ≤ d) (hscale : 1 ≤ (1 / 2 - a) * Real.sqrt x)
    (hprime :
      ∀ p : ℕ,
        p.Prime →
          AnalyticNumberTheory.Arithmetic.pairedEulerPrefixWeight (5 / 4) (11 / 4) (3 / 4) p ≤
            a * Real.log p + if p = 2 then d else 0)
    (hYcut : ∀ n ∈ Finset.Ioc 0 ⌊Y⌋₊, (n : ℝ) ≤ (99 / 40 : ℝ) * x)
    (hC : AnalyticNumberTheory.DirichletLFunction.twoPoleGammaConstant χ.primitiveCharacter ≤ C)
    (ht : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ (99 / 40 : ℝ) * x → χ p = 1) :
    (∑' n : ℕ, PaperStatements.gammaMellinKernel.summand χ.primitiveCharacter x n).re +
        gammaQuadraticLocalCorrection χ x ≤
      twoPoleConstantUpper A C x - twoPoleEulerPrefixMass (Finset.Ioc 0 ⌊Y⌋₊) + d +
        (q.primeFactors.card : ℝ) * Real.log ((99 / 40 : ℝ) * x) / Real.sqrt x := by
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hp := DirichletCharacter.primitiveCharacter_isPrimitive χ
  have hnp := AnalyticNumberTheory.Arithmetic.primitiveCharacter_ne_one χ hne
  have hm := NumberTheory.three_le_conductor_of_ne_one χ hne
  have hmA := (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level).trans hqA
  have hb :=
    PaperStatements.gamma_primitive_sum_re_le_twoPole_constant (le_max_left 20000 A) hm
      (hmA.trans (le_max_right 20000 A)) hGRH hp hnp (inv_ne_one.mpr hnp)
      (by linarith only [hx] : 2 ≤ x) hC (Finset.Ioc 0 ⌊Y⌋₊) (Finset.Ioc 0 ⌊Y⌋₊)
  have he :=
    AnalyticNumberTheory.Arithmetic.paired_euler_prefixes_eq_weight χ.primitiveCharacter (5 / 4)
      (11 / 4) (3 / 4) (Finset.Ioc 0 ⌊Y⌋₊)
  have hd :=
    AnalyticNumberTheory.Arithmetic.paired_weighted_sum_ge_quadratic_budget χ.primitiveCharacter
      (NumberTheory.isQuadratic_primitiveCharacter χ hquad) (Finset.Ioc 0 ⌊Y⌋₊)
      (AnalyticNumberTheory.Arithmetic.pairedEulerPrefixWeight (5 / 4) (11 / 4) (3 / 4)) hYcut
      (fun n _ hn ↦
        AnalyticNumberTheory.Arithmetic.pairedEulerPrefixWeight_eq_zero_of_mangoldt_eq_zero _ _ _
          hn)
      (fun n _ ↦
        AnalyticNumberTheory.Arithmetic.pairedEulerPrefixWeight_nonneg _ _ (by norm_num only) n)
      (fun p hp hb hc ↦
        PaperStatements.primitiveCharacter_apply_one_of_apply_one χ
          (ht p hp (hp.coprime_iff_not_dvd.mp hc) hb))
  have hbudget :=
    quadraticExcludedBudget_le_prefix_add_conductor_budget χ hY
      (AnalyticNumberTheory.Arithmetic.pairedEulerPrefixWeight (5 / 4) (11 / 4) (3 / 4))
      (AnalyticNumberTheory.Arithmetic.pairedEulerPrefixWeight_nonneg _ _ (by norm_num only))
      (fun n hn ↦
        AnalyticNumberTheory.Arithmetic.pairedEulerPrefixWeight_eq_zero_of_mangoldt_eq_zero _ _ _
          (ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn))
      (fun p hp ↦ AnalyticNumberTheory.Arithmetic.pairedEulerPrefixWeight_prime_pow_antitone hp) ha
      hd0 hprime
  have hx0 : 0 < x := by linarith only [hx]
  have hl :=
    gammaQuadraticLocalCorrection_absorb_conductor χ hquad hx0
      (by linarith only [hx] : 1 ≤ (99 / 40 : ℝ) * x) hscale
  have hlog :=
    Real.log_le_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))) (Nat.cast_le.mpr hqA)
  have hquot :=
    AnalyticNumberTheory.DirichletLFunction.log_level_eq_log_conductor_add_log_quotient χ
  have hqa := congrArg (fun t : ℝ ↦ a * t) hquot
  rw [mul_add] at hqa
  dsimp only [twoPoleConstantUpper, signedTwoPoleUpper, twoPoleEulerPrefixMass] at *
  linarith only [hb, he, hd, hbudget, hl, hlog, hquot, hqa]

/-- Under the parameterized conductor-prefix bounds, a saving g at most the principal prefix
minus d yields a negative unit-prime witness whenever the saved gap exceeds the level-prime
ramp cost. Combine the arithmetic and principal ramp comparisons, then exclude zero by
coprimality and one by contradiction. This is the witness consumer for arbitrary admissible
conductor allocations; no fixed threshold twenty-five or fixed prime-cost coefficient is used. -/
theorem exists_prime_neg_one_of_parameterized_conductor_prefix {q A : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hquad : χ.IsQuadratic) (hne : χ ≠ 1) (hqA : q ≤ A)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x C Y g a d : ℝ} (hx : 2 ≤ x)
    (hY : 1 ≤ Y) (ha : 0 ≤ a) (hd : 0 ≤ d) (hscale : 1 ≤ (1 / 2 - a) * Real.sqrt x)
    (hprime :
      ∀ p : ℕ,
        p.Prime →
          AnalyticNumberTheory.Arithmetic.pairedEulerPrefixWeight (5 / 4) (11 / 4) (3 / 4) p ≤
            a * Real.log p + if p = 2 then d else 0)
    (hYcut : ∀ n ∈ Finset.Ioc 0 ⌊Y⌋₊, (n : ℝ) ≤ (99 / 40 : ℝ) * x)
    (hC : AnalyticNumberTheory.DirichletLFunction.twoPoleGammaConstant χ.primitiveCharacter ≤ C)
    (hg : g ≤ twoPoleEulerPrefixMass (Finset.Ioc 0 ⌊Y⌋₊) - d)
    (hgap :
      (q.primeFactors.card : ℝ) * Real.log ((99 / 40 : ℝ) * x) / Real.sqrt x <
        twoPoleConstantGap A (C - g) x) :
    ∃ p : ℕ, p.Prime ∧ ¬p ∣ q ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ χ p = -1 := by
  classical
  have hex : ∃ p : ℕ, p.Prime ∧ ¬p ∣ q ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ χ p ≠ 1 := by
    by_contra hnone
    have ht : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ (99 / 40 : ℝ) * x → χ p = 1 := fun p hp hd hb ↦
      Classical.byContradiction (fun hv ↦ hnone ⟨p, hp, hd, hb, hv⟩)
    have hb :=
      gamma_primitive_add_local_le_of_parameterized_conductor_prefix χ hquad hne hqA hGRH hx hY ha
        hd hscale hprime hYcut hC ht
    have hP := gamma_level_one_sum_upper_variable hGRH.riemann (by linarith only [hx] : 1 ≤ x)
    have hT := gamma_ramp_sum_lower_paired hGRH.riemann (by linarith only [hx] : 1 ≤ x)
    have hN := gamma_ramp_no_witness_comparison χ hquad (by linarith only [hx] : 0 < x) ht
    dsimp only [twoPoleConstantGap, signedTwoPoleGap, twoPoleConstantUpper,
      signedTwoPoleUpper] at hgap hb
    linarith only [hb, hP, hT, hN, hgap, hg]
  obtain ⟨p, hp, hd, hb, hv⟩ := hex
  have hz : χ p ≠ 0 :=
    MulChar.apply_ne_zero_iff.mpr
      ((ZMod.isUnit_iff_coprime p q).mpr (hp.coprime_iff_not_dvd.mpr hd))
  refine ⟨p, hp, hd, hb, ?_⟩
  rcases hquad (p : ZMod q) with h0 | h1 | hm
  · exact False.elim (hz h0)
  · exact False.elim (hv h1)
  · exact hm

end PseudoPrime.LLS
