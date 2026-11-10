/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.UniformKorseltTriple
public import PseudoPrime.AnalyticNumberTheory.GRH.Definition
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFactorCases
import PseudoPrime.NumberTheory.PrimeFactorPairClassification

/-! # Factor classification for quarter-bound witnesses -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, witnesses for uniform triples, square divisors, and distinct
prime pairs imply a witness for every odd composite. The remaining factor
patterns are handled by the existing quarter-bound factor theorems; an
arbitrary cutoff above the quarter-square bound is allowed. -/
theorem quarter_of_factor_cases {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {X : ℝ}
    (h_uniform :
      UniformKorseltTriple n →
        ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n))
    (h_square :
      ∀ p : ℕ,
        p.Prime →
          p ^ 2 ∣ n →
          ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n))
    (h_pair :
      ∀ p q : ℕ,
        p.Prime →
          q.Prime →
          p < q →
          n = p * q →
          ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n))
    (hX : (1 / 4 : ℝ) * Real.log n ^ 2 ≤ X) :
    ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  by_cases hu : UniformKorseltTriple n
  · exact h_uniform hu
  by_cases hsq : ∃ p : ℕ, p.Prime ∧ p ^ 2 ∣ n
  · obtain ⟨p, hp, hd⟩ := hsq
    exact h_square p hp hd
  by_cases h4 : 4 ≤ ArithmeticFunction.cardFactors n
  · obtain ⟨r, hr, hb, hf⟩ := exists_prime_reject_quarter_four_factors hn ho hc h4 hGRH
    exact ⟨r, hr, hb.trans hX, hf⟩
  have hsf : Squarefree n :=
    Nat.squarefree_iff_prime_squarefree.mpr (fun p hp h ↦ hsq ⟨p, hp, (pow_two p).symm ▸ h⟩)
  have hlist : n.primeFactorsList.Nodup :=
    (Nat.squarefree_iff_nodup_primeFactorsList (Nat.ne_zero_of_lt hn)).mp hsf
  have heq : n.primeFactors.card = ArithmeticFunction.cardFactors n := by
    change n.primeFactorsList.toFinset.card = n.primeFactorsList.length
    exact List.toFinset_card_of_nodup hlist
  by_cases h3 : 3 ≤ ArithmeticFunction.cardFactors n
  · have hk : n.primeFactors.card = 3 := by
      rw [heq]
      exact Nat.le_antisymm (Nat.lt_succ_iff.mp (Nat.lt_of_not_ge h4)) h3
    obtain ⟨r, hr, hb, hf⟩ := exists_prime_reject_quarter_nonuniform_three hn ho hsf hk hu hGRH
    exact ⟨r, hr, hb.trans hX, hf⟩
  have hkpos := ArithmeticFunction.cardFactors_pos_iff_one_lt.mpr hn
  have hkne : ArithmeticFunction.cardFactors n ≠ 1 := fun h ↦
    hc (ArithmeticFunction.cardFactors_eq_one_iff_prime.mp h)
  have hk2 : 2 ≤ ArithmeticFunction.cardFactors n :=
    Nat.succ_le_of_lt (lt_of_le_of_ne (Nat.succ_le_of_lt hkpos) hkne.symm)
  have hkeq : ArithmeticFunction.cardFactors n = 2 :=
    Nat.le_antisymm (Nat.lt_succ_iff.mp (Nat.lt_of_not_ge h3)) hk2
  obtain ⟨p, q, hp, hq, hpq, hprod⟩ :=
    NumberTheory.exists_ordered_prime_pair_of_cardFactors_two hn hkeq
  rcases hpq.eq_or_lt with heq' | hlt
  · subst q
    exact False.elim (hsq ⟨p, hp, by rw [hprod, pow_two]⟩)
  exact h_pair p q hp hq hlt hprod

end PseudoPrime.PrimeTestBounds.MillerRabin
