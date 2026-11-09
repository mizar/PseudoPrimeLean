/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ExponentialRampSummation
public import PseudoPrime.LLS.GammaEulerGrowthChebyshev
public import PseudoPrime.Analysis.GammaEulerPositiveLowerBound
public import PseudoPrime.PrimeTestBounds.MillerRabin.GammaPolynomialBudget

/-! # Gamma prefix growth and witness transfer -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Input: RH, a>=900, b>=2a and arbitrary n,Q,x. Claim: the
actual MR budget gains at least (a/100)b^(-21/20). Use twice the positive
Euler block gain. Role: retain analytic savings at arbitrary admissible cutoffs. -/
theorem gammaSignedPrefixMRBudget_doubling_block_gain (hRH : RiemannHypothesis) {a b : ℕ}
    (ha : 900 ≤ a) (hratio : (2 : ℝ) * a ≤ b) (n Q : ℕ) (x : ℝ) :
    gammaSignedPrefixMRBudget n Q x b + ((a : ℝ) / 4) * (b : ℝ) ^ (-21 / 20 : ℝ) ≤
      gammaSignedPrefixMRBudget n Q x a := by
  have hp :=
    LLS.gammaEulerPrefix_growth_doubling_RH hRH ha hratio
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
        2 * (LLS.exponentialRampMangoldtSum x / Real.sqrt x) -
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
theorem gammaSignedBudget_block_gain_5_4_RH (hRH : RiemannHypothesis) {a b : ℕ} (ha : 10000 ≤ a)
    (hratio : (5 / 4 : ℝ) * a ≤ b) (n Q : ℕ) (x : ℝ) :
    gammaSignedPrefixMRBudget n Q x b + ((a : ℝ) / 100) * (b : ℝ) ^ (-21 / 20 : ℝ) ≤
      gammaSignedPrefixMRBudget n Q x a := by
  have hp :=
    LLS.gamma_euler_prefix_growth_5_4_RH hRH ha hratio
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
        2 * (LLS.exponentialRampMangoldtSum x / Real.sqrt x) -
            (∑' j : ℕ,
                LLS.PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x j).re +
          ((a : ℝ) / 100) * (b : ℝ) ^ (-21 / 20 : ℝ)) :
    ∃ p : ℕ,
      p.Prime ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hd := gammaSignedBudget_block_gain_5_4_RH hGRH.riemann ha hratio n n x
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
        2 * (LLS.exponentialRampMangoldtSum x / Real.sqrt x) -
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
        2 * (LLS.exponentialRampMangoldtSum x / Real.sqrt x) -
          (∑' k : ℕ,
              LLS.PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x k).re) :
    ∃ p : ℕ,
      p.Prime ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  exact
    exists_prime_witness_of_signed_prefix_gap hn hnOdd hnComposite hGRH hnlarge (le_refl n) hx
      (by exact_mod_cast (Nat.zero_le b)) hbx
      ((gammaSignedPrefixMRBudget_lt_of_prefix_growth hGRH.riemann n n x hab hC).trans hgap)

end PseudoPrime.PrimeTestBounds.MillerRabin
