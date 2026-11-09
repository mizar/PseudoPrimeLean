/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.GaussianPrefixComparison
public import PseudoPrime.PrimeTest.MillerRabin.Decomposition
public import PseudoPrime.NumberTheory.ResidueSubgroup
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianConductorConstant

/-! Witness extraction from a relative Gaussian prefix comparison. -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/--
Inputs: an odd ambient modulus at least 20000, a pass-containing subgroup, GRH,
a certified prefix, an admissible relative width and scale, and a refuted Gaussian comparison.
Claim: some prime below the enclosing cutoff rejects strong Miller-Rabin.
Proof: passing primes give both the divisor exclusion and subgroup containment required by
the actual relative-prefix comparison, contradicting the supplied numerical rejection.
Role: transports independently proved scalar budgets into actual rejecting-prime theorems.
-/
theorem gaussianRelative_witness {n N : ℕ} [NeZero n] (hnOdd : Odd n) (hnlarge : 20000 ≤ n)
    (H : Subgroup (ZMod n)ˣ)
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {P h x lambda B : ℝ}
    (hprefix : P ≤ ∑ j ∈ Finset.Ioc 0 N, Analysis.gaussianResolventMangoldtWeight j) (hh : 0 < h)
    (hh1 : h ≤ 1 / 2) (hx : 4 ≤ x) (hl : 0 ≤ lambda) (hX : N ≤ lambda * x) (hcut : lambda * x ≤ B)
    (hnot :
      ¬(((H.index : ℝ) * (1 - h) *
                (∫ u in (0 : ℝ)..lambda,
                  (LLS.PaperStatements.gaussianGammaMellinKernel.transform u).re / Real.sqrt u) -
              Real.exp (1 / 16 : ℝ)) *
            Real.sqrt x ≤
          gaussianConductorCoeff * LLS.PaperStatements.subgroupConductorLogSum H +
            (H.index : ℝ) *
              (1 / (10 * h) +
                ((21 / (10 * h) + 1839 / 1000) / Real.sqrt x) * Real.exp (1 / 16 : ℝ)) +
            13 +
            ((H.index - 1 : ℕ) : ℝ) * LLS.PaperStatements.gaussianPrefixError P n x)) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ B ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_contra hnone
  have hn1 : 1 < n := lt_of_lt_of_le (by decide : 1 < 20000) hnlarge
  have hpass :
    ∀ p : ℕ, p.Prime → (p : ℝ) ≤ lambda * x → PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
    intro p hp hb
    by_contra hf
    exact hnone ⟨p, hp, hb.trans hcut, hf⟩
  have hdiv : ∀ p : ℕ, p.Prime → p ∣ n → ⌊lambda * x⌋₊ < p := by
    intro p hp hpdvd
    apply lt_of_not_ge
    intro hfloor
    have hb : (p : ℝ) ≤ lambda * x := (Nat.le_floor_iff' hp.ne_zero).mp hfloor
    exact PrimeTest.strongMillerRabinPass_not_of_prime_dvd hn1 hnOdd hp hpdvd (hpass p hp hb)
  have hsmall :
    ∀ p : ℕ, p.Prime → ¬p ∣ n → (p : ℝ) ≤ lambda * x → NumberTheory.residueInSubgroup n H p := by
    intro p hp _ hb
    exact hHpass _ (hpass p hp hb)
  exact
    hnot
      (LLS.PaperStatements.gaussian_relative_prefix_le hprefix hnlarge H hGRH hh hh1 hx hl hX hdiv
        hsmall)

end PseudoPrime.PrimeTestBounds.MillerRabin
