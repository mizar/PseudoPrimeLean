/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaFourFifthsRetainedNumerics
public import PseudoPrime.LLS.GammaEulerGrowthChebyshev
public import PseudoPrime.Analysis.GammaEulerPositiveLowerBound
public import PseudoPrime.PrimeTestBounds.MillerRabin.GammaSeedPairedBounds

/-! # MR prime rejecting witnesses with coefficient 4/5 from log 12800 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Input: RH, L>=12800 and log(n)<=L. Claim: the prefix-50000 MR budget
is below the actual ramp-principal gap at x=(32/99)L². Keep the analytic
prefix 28493/5000 and combine the uniform errors with the strict main gap.
Role: lower the coefficient-four-fifths entrance without finite input checks. -/
theorem gammaSignedPrefixMRBudget_gap_four_fifths (hRH : RiemannHypothesis) {n : ℕ} {L : ℝ}
    (hL : 12800 ≤ L) (hlogn : Real.log n ≤ L) :
    let x := (32 / 99 : ℝ) * L ^ 2
    gammaSignedPrefixMRBudget n n x 50000 <
      2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) -
        (∑' k : ℕ,
            LLS.PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x k).re := by
  dsimp only
  let x := (32 / 99 : ℝ) * L ^ 2
  have hx : 1 ≤ x := by
    dsimp only [x]
    nlinarith only [hL, sq_nonneg (L - 12800)]
  have he :=
    LLS.gamma_four_fifths_error_budgets hL hx
      (Analysis.ramp_scale_sqrt_lower (by linarith only [hL] : 0 ≤ L))
      (LLS.gamma_four_fifths_cutoff_log hL)
  have hprefix := LLS.gamma_prefix50000_lower_asymmetric hRH (le_refl (50000 : ℝ))
  have hu := gammaSignedPrefixMRBudget_lt_precise_common_cost hRH n n x 50000
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

end PseudoPrime.PrimeTestBounds.MillerRabin

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Input: RH, a>=900, b>=2a and arbitrary n,Q,x. Claim: the
actual MR budget gains at least (a/100)b^(-21/20). Use twice the positive
Euler block gain. Role: retain analytic savings at arbitrary admissible cutoffs. -/
theorem gammaSignedPrefixMRBudget_doubling_block_gain (hRH : RiemannHypothesis) {a b : ℕ}
    (ha : 900 ≤ a) (hratio : (2 : ℝ) * a ≤ b) (n Q : ℕ) (x : ℝ) :
    gammaSignedPrefixMRBudget n Q x b + ((a : ℝ) / 4) * (b : ℝ) ^ (-21 / 20 : ℝ) ≤
      gammaSignedPrefixMRBudget n Q x a := by
  have hp :=
    LLS.gamma_euler_prefix_lower_growth_of_doubling_block hRH ha hratio
      (le_refl (∑ j ∈ Finset.Ioc 0 a, Analysis.gammaResolventMangoldtWeight j))
  dsimp only [gammaSignedPrefixMRBudget]
  simp only [Nat.floor_natCast]
  nlinarith only [hp]

/-- Input: GRH, odd composite n>=20000, an admissible scale and cutoffs
a>=900, b>=2a, and the displayed improved old-prefix gap. Claim:
a prime MR rejecting base is at most (99/40)x. Apply the actual analytic
budget gain before witness extraction. Role: expose the uniform short-block bound. -/
theorem exists_prime_witness_of_doubling_block_gap {n a b : ℕ} {x : ℝ} (hn : 1 < n) (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hnlarge : 20000 ≤ n) (hx : 2 ≤ x) (ha : 900 ≤ a) (hratio : (2 : ℝ) * a ≤ b)
    (hbx : (b : ℝ) ≤ (99 / 40 : ℝ) * x)
    (hgap :
      gammaSignedPrefixMRBudget n n x a <
        2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) -
            (∑' j : ℕ,
                LLS.PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x j).re +
          ((a : ℝ) / 4) * (b : ℝ) ^ (-21 / 20 : ℝ)) :
    ∃ p : ℕ,
      p.Prime ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hd := gammaSignedPrefixMRBudget_doubling_block_gain hGRH.riemann ha hratio n n x
  apply
    exists_prime_witness_of_signed_prefix_gap hn hnOdd hnComposite hGRH hnlarge (le_refl n) hx
      (by exact_mod_cast (Nat.zero_le b)) hbx
  linarith only [hd, hgap]

end PseudoPrime.PrimeTestBounds.MillerRabin

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Input: RH, a>=10000, b>=5a/4 and arbitrary n,Q,x. Claim: the
actual MR budget gains at least (a/100)b^(-21/20). Use twice the positive
Euler block gain. Role: retain analytic savings at arbitrary admissible cutoffs. -/
theorem gammaSignedPrefixMRBudget_five_fourths_block_gain (hRH : RiemannHypothesis) {a b : ℕ}
    (ha : 10000 ≤ a) (hratio : (5 / 4 : ℝ) * a ≤ b) (n Q : ℕ) (x : ℝ) :
    gammaSignedPrefixMRBudget n Q x b + ((a : ℝ) / 100) * (b : ℝ) ^ (-21 / 20 : ℝ) ≤
      gammaSignedPrefixMRBudget n Q x a := by
  have hp :=
    LLS.gamma_euler_prefix_lower_growth_of_five_fourths_block hRH ha hratio
      (le_refl (∑ j ∈ Finset.Ioc 0 a, Analysis.gammaResolventMangoldtWeight j))
  dsimp only [gammaSignedPrefixMRBudget]
  simp only [Nat.floor_natCast]
  nlinarith only [hp]

/-- Input: GRH, odd composite n>=20000, an admissible scale and cutoffs
a>=10000, b>=5a/4, and the displayed improved old-prefix gap. Claim:
a prime MR rejecting base is at most (99/40)x. Apply the actual analytic
budget gain before witness extraction. Role: expose the uniform short-block bound. -/
theorem exists_prime_witness_of_five_fourths_block_gap {n a b : ℕ} {x : ℝ} (hn : 1 < n)
    (hnOdd : Odd n) (hnComposite : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hnlarge : 20000 ≤ n)
    (hx : 2 ≤ x) (ha : 10000 ≤ a) (hratio : (5 / 4 : ℝ) * a ≤ b) (hbx : (b : ℝ) ≤ (99 / 40 : ℝ) * x)
    (hgap :
      gammaSignedPrefixMRBudget n n x a <
        2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) -
            (∑' j : ℕ,
                LLS.PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x j).re +
          ((a : ℝ) / 100) * (b : ℝ) ^ (-21 / 20 : ℝ)) :
    ∃ p : ℕ,
      p.Prime ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hd := gammaSignedPrefixMRBudget_five_fourths_block_gain hGRH.riemann ha hratio n n x
  apply
    exists_prime_witness_of_signed_prefix_gap hn hnOdd hnComposite hGRH hnlarge (le_refl n) hx
      (by exact_mod_cast (Nat.zero_le b)) hbx
  linarith only [hd, hgap]

end PseudoPrime.PrimeTestBounds.MillerRabin

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Input: RH and arbitrary n,Q,x. Claim: increasing the prefix from
50000 to 62500 reduces the actual MR budget by at least 1/20. Use the
analytic short-block gain. Role: strengthen existing gap comparisons. -/
theorem gammaSignedPrefixMRBudget_short_block_gain (hRH : RiemannHypothesis) (n Q : ℕ) (x : ℝ) :
    gammaSignedPrefixMRBudget n Q x 62500 + 1 / 20 ≤ gammaSignedPrefixMRBudget n Q x 50000 := by
  have hp :=
    LLS.gamma_euler_prefix_50000_62500_gain hRH
      (le_refl (∑ j ∈ Finset.Ioc 0 (50000 : ℕ), Analysis.gammaResolventMangoldtWeight j))
  dsimp only [gammaSignedPrefixMRBudget]
  norm_num only [Nat.floor_ofNat]
  linarith only [hp]

/-- Input: GRH, odd composite n>=20000, an admissible scale, and an old-prefix
gap allowing the new 1/20 saving. Claim: a prime MR rejecting base is at most
(99/40)x. Apply the actual budget decrease before witness extraction.
Role: make the short analytic block directly usable for witness bounds. -/
theorem exists_prime_witness_of_short_block_improved_gap {n : ℕ} {x : ℝ} (hn : 1 < n)
    (hnOdd : Odd n) (hnComposite : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hnlarge : 20000 ≤ n)
    (hx : 2 ≤ x) (hbx : (62500 : ℝ) ≤ (99 / 40 : ℝ) * x)
    (hgap :
      gammaSignedPrefixMRBudget n n x 50000 <
        2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) -
            (∑' j : ℕ,
                LLS.PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x j).re +
          1 / 20) :
    ∃ p : ℕ,
      p.Prime ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hd := gammaSignedPrefixMRBudget_short_block_gain hGRH.riemann n n x
  apply
    exists_prime_witness_of_signed_prefix_gap hn hnOdd hnComposite hGRH hnlarge (le_refl n) hx
      (by norm_num only : (0 : ℝ) ≤ 62500) hbx
  linarith only [hd, hgap]

end PseudoPrime.PrimeTestBounds.MillerRabin

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Input: GRH, odd composite n and log(n) >= 12800. Claim: a prime MR rejecting
base is at most (4/5)log(n)^2 and strictly below log(n)^2. Combine the retained
Euler prefix with the variable ramp bounds on the whole half-line.
Role: lower the coefficient-four-fifths entrance without finite input checks. -/
theorem exists_prime_witness_le_retained_four_fifths_gamma_log_12800 {n : ℕ} (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 12800 ≤ Real.log n) :
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
    nlinarith only [hL, sq_nonneg (Real.log n - 12800)]
  have hgap := gammaSignedPrefixMRBudget_gap_four_fifths hGRH.riemann hL (le_refl _)
  obtain ⟨p, hp, hb, hf⟩ :=
    exists_prime_witness_of_signed_prefix_gap hn hnOdd hnComposite hGRH hq (le_refl n) hx
      (by norm_num only : (0 : ℝ) ≤ 50000)
      (show (50000 : ℝ) ≤ (99 / 40 : ℝ) * x by
        dsimp only [x]
        nlinarith only [hL, sq_nonneg (Real.log n - 12800)])
      hgap
  have hsq : 0 < (Real.log n) ^ 2 := sq_pos_of_pos (by linarith only [hL])
  dsimp only [x] at hb
  refine ⟨p, hp, ?_, ?_, hf⟩
  · nlinarith only [hb]
  · nlinarith only [hb, hsq]

/-- Under the same GRH, odd-composite and log(n) >= 12800 hypotheses, a least
prime MR rejecting base satisfies the displayed bound. Minimize the unbounded
prime rejection predicate. Role: expose a least-witness version of the half-line bound. -/
theorem exists_least_prime_witness_le_retained_four_fifths_gamma_log_12800 {n : ℕ} (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 12800 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ (4 / 5 : ℝ) * (Real.log n) ^ 2 ∧
        ∀ r : ℕ, r.Prime → ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) → p ≤ r := by
  classical
  obtain ⟨p, hp, hb, _, hf⟩ :=
    exists_prime_witness_le_retained_four_fifths_gamma_log_12800 hnOdd hnComposite hGRH hL
  have hex : ∃ r : ℕ, r.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := ⟨p, hp, hf⟩
  exact
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2,
      (Nat.cast_le.mpr (Nat.find_min' hex ⟨hp, hf⟩)).trans hb, fun r hr hf ↦
      Nat.find_min' hex ⟨hr, hf⟩⟩

/-- Under the same hypotheses, a prime below the stated bound fails the initial
power equality and every negative-one equality in the standard binary decomposition
of n-1. Apply the characterization of MR rejection. Role: expose the actual power tests. -/
theorem exists_prime_rejecting_powers_le_retained_four_fifths_gamma_log_12800 {n : ℕ}
    (hnOdd : Odd n) (hnComposite : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 12800 ≤ Real.log n) :
    let (s, d) := Nat.maxPowDvdDiv 2 (n - 1);
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (4 / 5 : ℝ) * (Real.log n) ^ 2 ∧
        (p : ZMod n) ^ d ≠ 1 ∧ ∀ j : ℕ, j < s → (p : ZMod n) ^ (2 ^ j * d) ≠ -1 := by
  obtain ⟨p, hp, hb, _, hf⟩ :=
    exists_prime_witness_le_retained_four_fifths_gamma_log_12800 hnOdd hnComposite hGRH hL
  exact ⟨p, hp, hb, PrimeTest.not_strongMillerRabinPass_iff.mp hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Input: RH, ordered natural cutoffs and a proved Euler prefix credit at a.
Claim: the actual MR budget retains the additional signed Chebyshev block gain.
Insert the analytic prefix-growth bound into the exact common-cost comparison.
Role: improve variable-cutoff budgets without introducing finite prime data. -/
theorem gammaSignedPrefixMRBudget_lt_of_prefix_growth (hRH : RiemannHypothesis) (n Q : ℕ) (x : ℝ)
    {a b : ℕ} {C : ℝ} (hab : a ≤ b)
    (hC : C ≤ ∑ k ∈ Finset.Ioc 0 a, Analysis.gammaResolventMangoldtWeight k) :
    gammaSignedPrefixMRBudget n Q x b <
      (11783423 / 25000000 : ℝ) * Real.log n + 541 / 50 - 2 * C -
          (b : ℝ) ^ (-21 / 20 : ℝ) * (Chebyshev.psi b - Chebyshev.psi a) +
        ((7 / 6 : ℝ) * Real.log Q + 4) / Real.sqrt x +
        43 * x ^ (-9 / 16 : ℝ) := by
  have hg := Analysis.gamma_euler_prefix_lower_growth hab hC
  have hu := gammaSignedPrefixMRBudget_lt_precise_common_cost hRH n Q x b
  norm_num only [Nat.floor_natCast] at hu
  linarith only [hg, hu]

/-- Input: GRH, an odd composite n>=20000, admissible scale/cutoffs and the
displayed scalar gap after analytic prefix growth. Claim: a prime MR rejecting
base lies below (99/40)x. Transfer the explicit budget to actual witness extraction.
Role: connect the retained Chebyshev gain to prime witnesses. -/
theorem exists_prime_witness_of_prefix_growth_gap {n a b : ℕ} {x C : ℝ} (hn : 1 < n) (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hnlarge : 20000 ≤ n) (hx : 2 ≤ x) (hab : a ≤ b) (hbx : (b : ℝ) ≤ (99 / 40 : ℝ) * x)
    (hC : C ≤ ∑ k ∈ Finset.Ioc 0 a, Analysis.gammaResolventMangoldtWeight k)
    (hgap :
      (11783423 / 25000000 : ℝ) * Real.log n + 541 / 50 - 2 * C -
            (b : ℝ) ^ (-21 / 20 : ℝ) * (Chebyshev.psi b - Chebyshev.psi a) +
          ((7 / 6 : ℝ) * Real.log n + 4) / Real.sqrt x +
          43 * x ^ (-9 / 16 : ℝ) <
        2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) -
          (∑' k : ℕ,
              LLS.PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x k).re) :
    ∃ p : ℕ,
      p.Prime ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  exact
    exists_prime_witness_of_signed_prefix_gap hn hnOdd hnComposite hGRH hnlarge (le_refl n) hx
      (by exact_mod_cast (Nat.zero_le b)) hbx
      ((gammaSignedPrefixMRBudget_lt_of_prefix_growth hGRH.riemann n n x hab hC).trans hgap)

end PseudoPrime.PrimeTestBounds.MillerRabin

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Input: RH, L>=11800 and log(n)<=L. Claim: the prefix-102400000 MR budget
is below the actual ramp-principal gap at x=(32/99)L². Use nine symbolic
Euler-prefix doublings and the retained uniform errors. Role: connect the
positive Euler block gain to a smaller analytic entrance without finite input checks. -/
theorem gammaSignedPrefixMRBudget_gap_four_fifths_growing_prefix (hRH : RiemannHypothesis) {n : ℕ}
    {L : ℝ} (hL : 11800 ≤ L) (hlogn : Real.log n ≤ L) :
    let x := (32 / 99 : ℝ) * L ^ 2
    gammaSignedPrefixMRBudget n n x 102400000 <
      2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) -
        (∑' k : ℕ,
            LLS.PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x k).re := by
  dsimp only
  let x := (32 / 99 : ℝ) * L ^ 2
  have hx : 1 ≤ x := by
    dsimp only [x]
    nlinarith only [hL, sq_nonneg (L - 11800)]
  have he :=
    LLS.gamma_four_fifths_growing_error_budgets hL hx
      (Analysis.ramp_scale_sqrt_lower (by linarith only [hL] : 0 ≤ L))
      (LLS.gamma_four_fifths_growing_cutoff_log hL)
  have hprefix := LLS.gamma_prefix102400000_lower_halfline hRH (le_refl (102400000 : ℝ))
  have hu := gammaSignedPrefixMRBudget_lt_precise_common_cost hRH n n x 102400000
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

end PseudoPrime.PrimeTestBounds.MillerRabin

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Input: GRH, odd composite n and log(n) >= 11800. Claim: a prime MR rejecting
base is at most (4/5)log(n)^2 and strictly below log(n)^2. Combine the retained
Euler prefix with the variable ramp bounds on the whole half-line.
Role: lower the coefficient-four-fifths entrance without finite input checks. -/
theorem exists_prime_witness_le_growing_four_fifths_gamma_log_11800 {n : ℕ} (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 11800 ≤ Real.log n) :
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
    nlinarith only [hL, sq_nonneg (Real.log n - 11800)]
  have hgap := gammaSignedPrefixMRBudget_gap_four_fifths_growing_prefix hGRH.riemann hL (le_refl _)
  obtain ⟨p, hp, hb, hf⟩ :=
    exists_prime_witness_of_signed_prefix_gap hn hnOdd hnComposite hGRH hq (le_refl n) hx
      (by norm_num only : (0 : ℝ) ≤ 102400000)
      (show (102400000 : ℝ) ≤ (99 / 40 : ℝ) * x
        by
        dsimp only [x]
        nlinarith only [hL, sq_nonneg (Real.log n - 11800)])
      hgap
  have hsq : 0 < (Real.log n) ^ 2 := sq_pos_of_pos (by linarith only [hL])
  dsimp only [x] at hb
  refine ⟨p, hp, ?_, ?_, hf⟩
  · nlinarith only [hb]
  · nlinarith only [hb, hsq]

/-- Under the same GRH, odd-composite and log(n) >= 11800 hypotheses, a least
prime MR rejecting base satisfies the displayed bound. Minimize the unbounded
prime rejection predicate. Role: expose a least-witness version of the half-line bound. -/
theorem exists_least_prime_witness_le_growing_four_fifths_gamma_log_11800 {n : ℕ} (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 11800 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ (4 / 5 : ℝ) * (Real.log n) ^ 2 ∧
        ∀ r : ℕ, r.Prime → ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) → p ≤ r := by
  classical
  obtain ⟨p, hp, hb, _, hf⟩ :=
    exists_prime_witness_le_growing_four_fifths_gamma_log_11800 hnOdd hnComposite hGRH hL
  have hex : ∃ r : ℕ, r.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := ⟨p, hp, hf⟩
  exact
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2,
      (Nat.cast_le.mpr (Nat.find_min' hex ⟨hp, hf⟩)).trans hb, fun r hr hf ↦
      Nat.find_min' hex ⟨hr, hf⟩⟩

/-- Under the same hypotheses, a prime below the stated bound fails the initial
power equality and every negative-one equality in the standard binary decomposition
of n-1. Apply the characterization of MR rejection. Role: expose the actual power tests. -/
theorem exists_prime_rejecting_powers_le_growing_four_fifths_gamma_log_11800 {n : ℕ} (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 11800 ≤ Real.log n) :
    let (s, d) := Nat.maxPowDvdDiv 2 (n - 1);
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (4 / 5 : ℝ) * (Real.log n) ^ 2 ∧
        (p : ZMod n) ^ d ≠ 1 ∧ ∀ j : ℕ, j < s → (p : ZMod n) ^ (2 ^ j * d) ≠ -1 := by
  obtain ⟨p, hp, hb, _, hf⟩ :=
    exists_prime_witness_le_growing_four_fifths_gamma_log_11800 hnOdd hnComposite hGRH hL
  exact ⟨p, hp, hb, PrimeTest.not_strongMillerRabinPass_iff.mp hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
