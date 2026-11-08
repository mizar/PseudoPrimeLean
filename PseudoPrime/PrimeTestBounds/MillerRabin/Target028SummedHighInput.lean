/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028SummedCells
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Through1133

/-! # Squarefree semiprime input for the refined count -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A squarefree odd composite with fewer than four prime factors and not
exactly three is a distinct semiprime. The refined grouped cells then
give a 0.28 witness on logarithmic scales from 88.181 through 96.708. -/
theorem target028_squarefree_summed_high {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hsf : Squarefree n) (h4 : ¬4 ≤ ArithmeticFunction.cardFactors n) (h3 : n.primeFactors.card ≠ 3)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (88181 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 96708 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hlist : n.primeFactorsList.Nodup :=
    (Nat.squarefree_iff_nodup_primeFactorsList (Nat.ne_zero_of_lt hn)).mp hsf
  have heq : n.primeFactors.card = ArithmeticFunction.cardFactors n := by
    change n.primeFactorsList.toFinset.card = n.primeFactorsList.length
    exact List.toFinset_card_of_nodup hlist
  have hkpos := ArithmeticFunction.cardFactors_pos_iff_one_lt.mpr hn
  have hkne : ArithmeticFunction.cardFactors n ≠ 1 := fun h ↦
    hc (ArithmeticFunction.cardFactors_eq_one_iff_prime.mp h)
  have hk2 : 2 ≤ ArithmeticFunction.cardFactors n :=
    Nat.succ_le_of_lt (lt_of_le_of_ne (Nat.succ_le_of_lt hkpos) hkne.symm)
  have hkle : ArithmeticFunction.cardFactors n ≤ 3 := Nat.lt_succ_iff.mp (Nat.lt_of_not_ge h4)
  have hkne3 : ArithmeticFunction.cardFactors n ≠ 3 := fun h ↦ h3 (heq.trans h)
  have hkeq : ArithmeticFunction.cardFactors n = 2 :=
    Nat.le_antisymm (Nat.lt_succ_iff.mp (lt_of_le_of_ne hkle hkne3)) hk2
  obtain ⟨p, q, hp, hq, hpq, hprod⟩ :=
    NumberTheory.exists_ordered_prime_pair_of_cardFactors_two hn hkeq
  rcases hpq.eq_or_lt with heqp | hlt
  · subst q
    have hndiv := (Nat.squarefree_iff_prime_squarefree.mp hsf) p hp
    exact False.elim (hndiv (by rw [hprod]))
  · exact target028_semiprime_88181_96708 hn ho hp hq hlt hprod hGRH hL hU

end PseudoPrime.PrimeTestBounds.MillerRabin
