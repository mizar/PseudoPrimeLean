/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GammaRetainedFourFifthsBounds
public import PseudoPrime.LLS.GammaFourFifthsLeadingNumerics
public import PseudoPrime.LLS.GammaEulerLeadingGrowth

/-! # Coefficient-four-fifths MR witnesses from logarithmic level 11255 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Input: RH, L>=11255 and log(n)<=L. Claim: the prefix-100000000 MR budget
is below the actual ramp-principal gap at x=(32/99)L². Use nine weighted
Euler-prefix doublings and one partial block and the retained uniform errors. Role: connect the
positive Euler block gain to a smaller analytic entrance without finite input checks. -/
theorem gammaSignedPrefixMRBudget_gap_four_fifths_leading_prefix (hRH : RiemannHypothesis) {n : ℕ}
    {L : ℝ} (hL : 11255 ≤ L) (hlogn : Real.log n ≤ L) :
    let x := (32 / 99 : ℝ) * L ^ 2
    gammaSignedPrefixMRBudget n n x 100000000 <
      2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) -
        (∑' k : ℕ,
            LLS.PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x k).re := by
  dsimp only
  let x := (32 / 99 : ℝ) * L ^ 2
  have hx : 1 ≤ x := by
    dsimp only [x]
    nlinarith only [hL, sq_nonneg (L - 11255)]
  have he :=
    LLS.gamma_four_fifths_leading_error_budgets hL hx
      (Analysis.ramp_scale_sqrt_lower (by linarith only [hL] : 0 ≤ L))
      (LLS.gamma_four_fifths_leading_cutoff_log hL)
  have hprefix := LLS.gamma_prefix100000000_lower_leading hRH (le_refl (100000000 : ℝ))
  have hu := gammaSignedPrefixMRBudget_lt_precise_common_cost hRH n n x 100000000
  have hpole : ((7 / 6 : ℝ) * Real.log n + 4) / Real.sqrt x ≤ 21 / 10 :=
    (div_le_div_of_nonneg_right
          (by linarith only [hlogn] : (7 / 6 : ℝ) * Real.log n + 4 ≤ (7 / 6 : ℝ) * L + 4)
          (Real.sqrt_nonneg x)).trans
      he.2.1
  have hP := LLS.gamma_level_one_sum_upper_variable hRH hx
  have hT := LLS.gamma_ramp_sum_lower_variable hRH hx
  have hm := Analysis.nonOne_main_term_gap (by linarith only [hL] : 0 < L)
  change
    _ < (2 * (∫ u in (0 : ℝ)..(99 / 40), Analysis.exponentialRampWeight u) - 1) * Real.sqrt x at hm
  nlinarith only [hu, hprefix, hpole, he.1, hP, hT, he.2.2.1, he.2.2.2, hm, hL, hlogn]

/-- Input: GRH, odd composite n and log(n) >= 11255. Claim: a prime MR rejecting
base is at most (4/5)log(n)^2 and strictly below log(n)^2. Combine the retained
Euler prefix with the variable ramp bounds on the whole half-line.
Role: lower the coefficient-four-fifths entrance without finite input checks. -/
theorem exists_prime_witness_le_leading_four_fifths_gamma_log_11255 {n : ℕ} (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 11255 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (4 / 5 : ℝ) * (Real.log n) ^ 2 ∧
        (p : ℝ) < (Real.log n) ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let : NeZero n := ⟨hnOdd.pos.ne'⟩
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hnOdd.pos
  have ht := Real.log_le_sub_one_of_pos hn0
  have hn : 1 < n := by exact_mod_cast (show (1 : ℝ) < n by linarith only [ht, hL])
  have hq : 20000 ≤ n := by
    by_contra hq
    have hnR : (n : ℝ) ≤ 46000 := by
      exact_mod_cast (show n ≤ 46000 by linarith only [lt_of_not_ge hq])
    have hl := Real.log_le_log hn0 hnR
    linarith only [hl, Analysis.log_46000_lt_eleven, hL]
  let x := (32 / 99 : ℝ) * (Real.log n) ^ 2
  have hx : 2 ≤ x := by
    dsimp only [x]
    nlinarith only [hL, sq_nonneg (Real.log n - 11255)]
  have hgap := gammaSignedPrefixMRBudget_gap_four_fifths_leading_prefix hGRH.riemann hL (le_refl _)
  obtain ⟨p, hp, hb, hf⟩ :=
    exists_prime_witness_of_signed_prefix_gap hn hnOdd hnComposite hGRH hq (le_refl n) hx
      (by norm_num only : (0 : ℝ) ≤ 100000000)
      (show (100000000 : ℝ) ≤ (99 / 40 : ℝ) * x
        by
        dsimp only [x]
        nlinarith only [hL, sq_nonneg (Real.log n - 11255)])
      hgap
  have hsq : 0 < (Real.log n) ^ 2 := sq_pos_of_pos (by linarith only [hL])
  dsimp only [x] at hb
  refine ⟨p, hp, ?_, ?_, hf⟩
  · nlinarith only [hb]
  · nlinarith only [hb, hsq]

/-- Under the same GRH, odd-composite and log(n) >= 11255 hypotheses, a least
prime MR rejecting base satisfies the displayed bound. Minimize the unbounded
prime rejection predicate. Role: expose a least-witness version of the half-line bound. -/
theorem exists_least_prime_witness_le_leading_four_fifths_gamma_log_11255 {n : ℕ} (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 11255 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ (4 / 5 : ℝ) * (Real.log n) ^ 2 ∧
        ∀ r : ℕ, r.Prime → ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) → p ≤ r := by
  classical
  obtain ⟨p, hp, hb, _, hf⟩ :=
    exists_prime_witness_le_leading_four_fifths_gamma_log_11255 hnOdd hnComposite hGRH hL
  have hex : ∃ r : ℕ, r.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := ⟨p, hp, hf⟩
  exact
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2,
      (Nat.cast_le.mpr (Nat.find_min' hex ⟨hp, hf⟩)).trans hb, fun r hr hf ↦
      Nat.find_min' hex ⟨hr, hf⟩⟩

/-- Under the same hypotheses, a prime below the stated bound fails the initial
power equality and every negative-one equality in the standard binary decomposition
of n-1. Apply the characterization of MR rejection. Role: expose the actual power tests. -/
theorem exists_prime_rejecting_powers_le_leading_four_fifths_gamma_log_11255 {n : ℕ} (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 11255 ≤ Real.log n) :
    let (s, d) := Nat.maxPowDvdDiv 2 (n - 1);
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (4 / 5 : ℝ) * (Real.log n) ^ 2 ∧
        (p : ZMod n) ^ d ≠ 1 ∧ ∀ j : ℕ, j < s → (p : ZMod n) ^ (2 ^ j * d) ≠ -1 := by
  obtain ⟨p, hp, hb, _, hf⟩ :=
    exists_prime_witness_le_leading_four_fifths_gamma_log_11255 hnOdd hnComposite hGRH hL
  exact ⟨p, hp, hb, PrimeTest.not_strongMillerRabinPass_iff.mp hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
