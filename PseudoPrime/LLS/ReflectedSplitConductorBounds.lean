/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ParameterizedConductorPrefixBounds
public import PseudoPrime.LLS.CertifiedRampPrincipalBounds

/-! # Conductor allocation with the split reflected error and certified ramp mass -/

@[expose] public section

namespace PseudoPrime.LLS

/-- For a quadratic nonprincipal character under GRH, allocate the Euler and local costs
against the exact logarithmic conductor saving. Assume a nonnegative prime cost a with
a prime-two allowance d and (1/2-a)sqrt x at least one. Under unit-prime triviality,
the upper cap retains the full principal prefix minus d. Use the split reflected Euler
remainder and discard only the nonpositive conductor term. This strengthens the arithmetic
input to negative-witness extraction without changing the conductor allocation. -/
theorem gamma_primitive_add_local_le_reflectedSplit_conductor_prefix {q A : ℕ} [NeZero q]
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
      reflectedSplitUpper A C x - twoPoleEulerPrefixMass (Finset.Ioc 0 ⌊Y⌋₊) + d +
        (q.primeFactors.card : ℝ) * Real.log ((99 / 40 : ℝ) * x) / Real.sqrt x := by
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hp := DirichletCharacter.primitiveCharacter_isPrimitive χ
  have hnp := AnalyticNumberTheory.Arithmetic.primitiveCharacter_ne_one χ hne
  have hm := NumberTheory.three_le_conductor_of_ne_one χ hne
  have hmA := (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level).trans hqA
  have hb :=
    PaperStatements.gamma_primitive_sum_re_le_twoPole_reflected_split (le_max_left 20000 A) hm
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
  have hc := Analysis.gammaNegativeConductorTerm_nonpos (Real.log_natCast_nonneg χ.conductor) hx0
  dsimp only [reflectedSplitUpper, twoPoleEulerPrefixMass] at *
  linarith only [hb, he, hd, hbudget, hl, hlog, hquot, hqa, hc]

/-- Under GRH and an admissible conductor allocation, a variable-width principal gap
above the level-prime cost yields a unit-prime witness of value minus one. Assume an
admissible width and a certified lower saving g on the full Euler prefix minus d.
Combine the split reflected upper cap with the actual principal lower bound, then exclude
zero by coprimality and one by contradiction. This connects both error improvements to
the negative-witness consumer. -/
theorem exists_prime_neg_one_of_variableRamp_reflectedSplit_conductor_prefix {q A : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hquad : χ.IsQuadratic) (hne : χ ≠ 1) (hqA : q ≤ A)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x C Y g a d h : ℝ} (hx : 2 ≤ x)
    (hh : 0 < h) (hhx : h ≤ x) (hY : 1 ≤ Y) (ha : 0 ≤ a) (hd : 0 ≤ d)
    (hscale : 1 ≤ (1 / 2 - a) * Real.sqrt x)
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
        variableRampPrincipalLower x h - reflectedSplitUpper A (C - g) x) :
    ∃ p : ℕ, p.Prime ∧ ¬p ∣ q ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ χ p = -1 := by
  classical
  have hex : ∃ p : ℕ, p.Prime ∧ ¬p ∣ q ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ χ p ≠ 1 := by
    by_contra hnone
    have ht : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ (99 / 40 : ℝ) * x → χ p = 1 := fun p hp hd hb ↦
      Classical.byContradiction (fun hv ↦ hnone ⟨p, hp, hd, hb, hv⟩)
    have hb :=
      gamma_primitive_add_local_le_reflectedSplit_conductor_prefix χ hquad hne hqA hGRH hx hY ha hd
        hscale hprime hYcut hC ht
    have hJ :=
      variableRampPrincipalLower_le_actual hGRH.riemann (by linarith only [hx] : 1 ≤ x) hh hhx
    have hN := gamma_ramp_no_witness_comparison χ hquad (by linarith only [hx] : 0 < x) ht
    dsimp only [reflectedSplitUpper] at hgap hb
    linarith only [hb, hJ, hN, hgap, hg]
  obtain ⟨p, hp, hd, hb, hv⟩ := hex
  have hz : χ p ≠ 0 :=
    MulChar.apply_ne_zero_iff.mpr
      ((ZMod.isUnit_iff_coprime p q).mpr (hp.coprime_iff_not_dvd.mpr hd))
  refine ⟨p, hp, hd, hb, ?_⟩
  rcases hquad (p : ZMod q) with h0 | h1 | hm
  · exact False.elim (hz h0)
  · exact False.elim (hv h1)
  · exact hm

/-- Under GRH, a quadratic nonprincipal character has a negative unit-prime witness when
the explicit variable-width gap exceeds its level-prime cost. Assume x at least 25, an
admissible width, and an Euler cutoff b at least 128 below the witness cutoff. Use the
certified anchor, the prime cost 3/10 with its prime-two allowance, and the mass 133/160.
This removes all unverified prefix and conductor-allocation premises from the consumer. -/
theorem exists_prime_neg_one_of_anchor128_mass133 {q A : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hquad : χ.IsQuadratic) (hne : χ ≠ 1) (hqA : q ≤ A)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x C b h : ℝ} (hx : 25 ≤ x)
    (hh : 0 < h) (hhx : h ≤ x) (hb : 128 ≤ b) (hcut : b ≤ (99 / 40 : ℝ) * x)
    (hC : AnalyticNumberTheory.DirichletLFunction.twoPoleGammaConstant χ.primitiveCharacter ≤ C)
    (hgap :
      (q.primeFactors.card : ℝ) * Real.log ((99 / 40 : ℝ) * x) / Real.sqrt x <
        (133 / 160 : ℝ) * Real.sqrt x - variableRampPrincipalErrorNumerator x h / Real.sqrt x -
              reflectedSplitUpper A C x +
            ((3643 / 1000 : ℝ) - 5 * b ^ (-1 / 4 : ℝ)) -
          (1 / 5 : ℝ) * Real.log 2) :
    ∃ p : ℕ, p.Prime ∧ ¬p ∣ q ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ χ p = -1 := by
  have hx0 : 0 ≤ x := by linarith only [hx]
  have hs : 5 ≤ Real.sqrt x := by nlinarith only [hx, Real.sq_sqrt hx0, Real.sqrt_nonneg x]
  have hp := pairedEulerPrefix_ge_anchor128 hGRH.riemann hb
  have hl := variableRampPrincipalLower_ge_133_160 x h
  apply
    exists_prime_neg_one_of_variableRamp_reflectedSplit_conductor_prefix χ hquad hne hqA hGRH
      (by linarith only [hx]) hh hhx (Y := b) (by linarith only [hb]) (a := 3 / 10) (d :=
      (1 / 5 : ℝ) * Real.log 2) (by norm_num only)
      (mul_nonneg (by norm_num only) (Real.log_natCast_nonneg 2)) (by linarith only [hs])
      (fun p hp ↦
        AnalyticNumberTheory.Arithmetic.pairedEulerPrefixWeight_prime_upper_three_tenths hp)
      (fun n hn ↦
        (Nat.cast_le.mpr (Finset.mem_Ioc.mp hn).2).trans
          ((Nat.floor_le (by linarith only [hb] : 0 ≤ b)).trans hcut))
      hC (g := (3643 / 1000 : ℝ) - 5 * b ^ (-1 / 4 : ℝ) - (1 / 5 : ℝ) * Real.log 2)
      (by linarith only [hp])
  dsimp only [reflectedSplitUpper]
  dsimp only [reflectedSplitUpper] at hgap
  linarith only [hgap, hl]

end PseudoPrime.LLS
