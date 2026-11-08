/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Through1076
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Square115
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028ElevenSupply

/-! # Coefficient 0.28 through logarithmic scale 11.33 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, every odd composite whose logarithm lies between 8 and 10.76
has a 0.28 rejecting prime. The square, factor-count, uniform Korselt and
eleven-prime semiprime branches cover the input alternatives. -/
theorem exists_prime_reject_028_through1133 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 1133 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  by_cases hfirst : Real.log n ≤ 269 / 25
  · exact exists_prime_reject_028_through1076 hn ho hc hGRH hL hfirst
  have h94 : (51 / 5 : ℝ) ≤ Real.log n := by linarith only [hfirst]
  by_cases hu : UniformKorseltTriple n
  · exact uniformKorselt_reject_028_8_30 hn ho hu hGRH hL (by linarith only [hU])
  by_cases hsq : ∃ p : ℕ, p.Prime ∧ p ^ 2 ∣ n
  · obtain ⟨p, hp, hd⟩ := hsq
    exact exists_prime_reject_028_square_through115 hn ho hp hd h94 (by linarith only [hU])
  by_cases h4 : 4 ≤ ArithmeticFunction.cardFactors n
  · exact exists_prime_reject_028_four_factors hn ho hc h4 hGRH
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
    exact exists_prime_reject_028_nonuniform_three hn ho hsf hk hu hGRH
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
  by_cases h1 : Real.log n ≤ 543 / 50
  · exact target028_eleven_cell56 hn ho hp hq hlt hprod hGRH (le_of_not_ge hfirst) h1
  by_cases h2 : Real.log n ≤ 1101 / 100
  · exact target028_eleven_cell57 hn ho hp hq hlt hprod hGRH (le_of_not_ge h1) h2
  by_cases h3' : Real.log n ≤ 1117 / 100
  · exact target028_eleven_cell58 hn ho hp hq hlt hprod hGRH (le_of_not_ge h2) h3'
  · exact target028_eleven_cell59 hn ho hp hq hlt hprod hGRH (le_of_not_ge h3') hU

end PseudoPrime.PrimeTestBounds.MillerRabin
