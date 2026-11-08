/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.UniformKorseltTriple
public import PseudoPrime.PrimeTestBounds.MillerRabin.LocalEvenAnchors
public import PseudoPrime.PrimeTestBounds.MillerRabin.TotalFactorWitnessBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.MixedTwoAdicLogBounds

/-! # Factor-count cases with coefficient 0.28 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, an odd composite with at least four prime factors counted with
multiplicity has a rejecting prime below the 0.28 bound. The total-factor estimate
has coefficient at most one quarter. -/
theorem exists_prime_reject_028_four_factors {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hk : 4 ≤ ArithmeticFunction.cardFactors n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  obtain ⟨p, hp, hb, hf⟩ := exists_prime_witness_le_cardFactors_log_sq hn ho hc hGRH
  have hkR : (4 : ℝ) ≤ ArithmeticFunction.cardFactors n := by exact_mod_cast hk
  have hden : (16 : ℝ) ≤ (ArithmeticFunction.cardFactors n : ℝ) ^ 2 := by nlinarith only [hkR]
  have hcoef : (4 : ℝ) / (ArithmeticFunction.cardFactors n : ℝ) ^ 2 ≤ 7 / 25 := by
    apply (div_le_iff₀ (by linarith only [hden])).2
    nlinarith only [hden]
  exact ⟨p, hp, hb.trans (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)), hf⟩

/-- Under GRH, an odd input with at least three distinct prime factors and a
marked local factor has a rejecting prime below the 0.28 bound. The marked-factor
estimate has coefficient at most one quarter. -/
theorem exists_prime_reject_028_local_factor {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hc : 3 ≤ n.primeFactors.card)
    (hlocal :
      (∃ r ∈ n.primeFactors, ∃ s ∈ n.primeFactors, padicValNat 2 (s - 1) < padicValNat 2 (r - 1)) ∨
        ∃ r ∈ n.primeFactors, ¬r - 1 ∣ n - 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  obtain ⟨p, hp, hf, hb, _⟩ := exists_leastWitness_le_local_factor_coefficient hn ho hc hlocal hGRH
  have hcR : (3 : ℝ) ≤ n.primeFactors.card := by exact_mod_cast hc
  have hden : (16 : ℝ) ≤ ((n.primeFactors.card : ℝ) + 1) ^ 2 := by nlinarith only [hcR]
  have hcoef : (4 : ℝ) / ((n.primeFactors.card : ℝ) + 1) ^ 2 ≤ 7 / 25 := by
    apply (div_le_iff₀ (by linarith only [hden])).2
    nlinarith only [hden]
  exact ⟨p, hp, hb.trans (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)), hf⟩

/-- Under GRH, a squarefree odd integer with exactly three distinct prime factors
has a rejecting prime below the 0.28 bound unless it is a uniform Korselt triple.
Failure of the exceptional conditions supplies a marked local factor. -/
theorem exists_prime_reject_028_nonuniform_three {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hsf : Squarefree n) (hc : n.primeFactors.card = 3) (hu : ¬UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
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
  exact exists_prime_reject_028_local_factor hn ho hc.ge hlocal hGRH

end PseudoPrime.PrimeTestBounds.MillerRabin
