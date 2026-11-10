/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.UniformKorseltTriple
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFourFactors
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMarkedFactor

/-! # Factor-count cases with coefficient one quarter -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, a squarefree odd integer with exactly three distinct prime factors
has a rejecting prime below the one-quarter bound unless it is a uniform Korselt triple.
Failure of the exceptional conditions supplies a marked local factor. -/
theorem exists_prime_reject_quarter_nonuniform_three {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hsf : Squarefree n) (hc : n.primeFactors.card = 3) (hu : ¬UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (1 / 4 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  classical
  have hlocal :
    (∃ r ∈ n.primeFactors, ∃ s ∈ n.primeFactors, padicValNat 2 (s - 1) < padicValNat 2 (r - 1)) ∨
      ∃ r ∈ n.primeFactors, ¬r - 1 ∣ n - 1 := by
    by_contra h
    have hK : ∀ p : ℕ, p.Prime → p ∣ n → p - 1 ∣ n - 1 := by
      intro p hp hd
      by_contra hbad
      exact h (Or.inr ⟨p, Nat.mem_primeFactors.mpr ⟨hp, hd, Nat.ne_zero_of_lt hn⟩, hbad⟩)
    have hV :
      ∀ p q : ℕ,
        p.Prime → q.Prime → p ∣ n → q ∣ n → padicValNat 2 (p - 1) = padicValNat 2 (q - 1) := by
      intro p q hp hq hpd hqd
      have hpm := Nat.mem_primeFactors.mpr ⟨hp, hpd, Nat.ne_zero_of_lt hn⟩
      have hqm := Nat.mem_primeFactors.mpr ⟨hq, hqd, Nat.ne_zero_of_lt hn⟩
      apply le_antisymm
      · exact Nat.le_of_not_gt (fun hv ↦ h (Or.inl ⟨p, hpm, q, hqm, hv⟩))
      · exact Nat.le_of_not_gt (fun hv ↦ h (Or.inl ⟨q, hqm, p, hpm, hv⟩))
    exact hu ⟨hsf, hc, hK, hV⟩
  exact exists_prime_reject_quarter_local_factor hn ho hc.ge hlocal hGRH

end PseudoPrime.PrimeTestBounds.MillerRabin
