/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030ThreeLow
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030EarlyCells
public import PseudoPrime.NumberTheory.PrimeFactorPairClassification
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030High
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030Local
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030SquareFirst
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030SquareExtended
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030SquareLog10

/-! # Combining low-scale factor branches for the 0.30 target -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, an odd composite with no squared prime divisor has a rejecting
prime within the 0.30 target on `[8, 10.059]`. The factor-count split joins the
six semiprime cells to the direct three-factor witness. -/
theorem exists_prime_reject_03_nosquare_low {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hsq : ∀ p : ℕ, p.Prime → ¬p ^ 2 ∣ n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 10059 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  by_cases hk : 3 ≤ ArithmeticFunction.cardFactors n
  · exact exists_prime_reject_03_three_low hn ho hk hL (by linarith only [hU])
  · have hkpos := ArithmeticFunction.cardFactors_pos_iff_one_lt.mpr hn
    have hkne : ArithmeticFunction.cardFactors n ≠ 1 := fun h ↦
      hc (ArithmeticFunction.cardFactors_eq_one_iff_prime.mp h)
    have hk2 : 2 ≤ ArithmeticFunction.cardFactors n :=
      Nat.succ_le_of_lt (lt_of_le_of_ne (Nat.succ_le_of_lt hkpos) hkne.symm)
    have hkeq : ArithmeticFunction.cardFactors n = 2 :=
      Nat.le_antisymm (Nat.lt_succ_iff.mp (Nat.lt_of_not_ge hk)) hk2
    obtain ⟨p, q, hp, hq, hpq, hprod⟩ :=
      NumberTheory.exists_ordered_prime_pair_of_cardFactors_two hn hkeq
    rcases hpq.eq_or_lt with heq | hlt
    · subst q
      exact False.elim (hsq p hp (by rw [hprod, pow_two]))
    · exact exists_prime_reject_03_semiprime_log10 hn ho hp hq hlt hprod hGRH hL hU

/-- Under GRH, a uniform Korselt triple has a 0.30 rejecting prime on the
two low-scale ranges `[8, 52/5]` and `[15, 197/5]`. The first range uses a
prime divisor and the second uses the certified local correction cover. -/
theorem exists_prime_reject_03_uniform_low {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (8 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 197 / 5)
    (hcover : Real.log n ≤ 52 / 5 ∨ 15 ≤ Real.log n) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hk : 3 ≤ ArithmeticFunction.cardFactors n := by
    have h := List.toFinset_card_le n.primeFactorsList
    change n.primeFactors.card ≤ ArithmeticFunction.cardFactors n at h
    exact hu.2.1 ▸ h
  rcases hcover with hlow | hhigh
  · exact exists_prime_reject_03_three_low hn ho hk hL hlow
  · exact exists_prime_reject_03_three_factors hn ho hGRH hk hhigh hU

/-- Under GRH, every odd composite with logarithm in `[8, 8.3]` has a
rejecting prime within the 0.30 target. Split by the presence of a squared
prime divisor and apply the weighted square or squarefree-factor branch. -/
theorem exists_prime_reject_03_log8_to_83 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 83 / 10) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  by_cases hsq : ∃ p : ℕ, p.Prime ∧ p ^ 2 ∣ n
  · obtain ⟨p, hp, hd⟩ := hsq
    exact exists_prime_reject_03_square_first hn ho hp hd hL hU
  · exact
      exists_prime_reject_03_nosquare_low hn ho hc (fun p hp hd ↦ hsq ⟨p, hp, hd⟩) hGRH hL
        (by linarith only [hU])

/-- Under GRH, every odd composite with logarithm in `[8, 9.4]` has a
rejecting prime within the 0.30 target. The extended weighted square-factor
certificate joins the existing nonsquare and three-factor branches. -/
theorem exists_prime_reject_03_log8_to_94 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 47 / 5) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  by_cases hsq : ∃ p : ℕ, p.Prime ∧ p ^ 2 ∣ n
  · obtain ⟨p, hp, hd⟩ := hsq
    exact exists_prime_reject_03_square_extended hn ho hp hd hL hU
  · exact
      exists_prime_reject_03_nosquare_low hn ho hc (fun p hp hd ↦ hsq ⟨p, hp, hd⟩) hGRH hL
        (by linarith only [hU])

/-- Under GRH, every odd composite with logarithm in `[8, 10.059]` has a
rejecting prime within the 0.30 target. The weighted square-factor certificate
and the squarefree factor split cover the same closed interval. -/
theorem exists_prime_reject_03_log8_to_10059 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 10059 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  by_cases hsq : ∃ p : ℕ, p.Prime ∧ p ^ 2 ∣ n
  · obtain ⟨p, hp, hd⟩ := hsq
    exact exists_prime_reject_03_square_log10 hn ho hp hd hL hU
  · exact exists_prime_reject_03_nosquare_low hn ho hc (fun p hp hd ↦ hsq ⟨p, hp, hd⟩) hGRH hL hU

end PseudoPrime.PrimeTestBounds.MillerRabin
