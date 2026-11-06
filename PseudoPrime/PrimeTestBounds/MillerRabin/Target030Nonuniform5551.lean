/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030Square805
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030Semiprime5551

/-! # Nonuniform 0.30 coverage through logarithmic scale 55.51 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, a squarefree nonuniform odd composite with logarithm in
`[8, 55.51]` has a 0.30 rejecting prime. The semiprime and unrestricted
nonuniform multi-factor bounds cover the two cases. -/
theorem exists_prime_reject_03_nonuniform_sf5551 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hsf : Squarefree n) (hu : ¬UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 5551 / 100) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (3 / 10 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_cases hcard : 3 ≤ n.primeFactors.card
  · exact exists_prime_reject_03_nonuniform_factors hn ho hc hsf hcard hu hGRH
  · have hk : ArithmeticFunction.cardFactors n = 2 := by
      have hlist : n.primeFactorsList.Nodup :=
        (Nat.squarefree_iff_nodup_primeFactorsList (Nat.ne_zero_of_lt hn)).mp hsf
      have heq : n.primeFactors.card = ArithmeticFunction.cardFactors n := by
        change n.primeFactorsList.toFinset.card = n.primeFactorsList.length
        exact List.toFinset_card_of_nodup hlist
      have hpos := ArithmeticFunction.cardFactors_pos_iff_one_lt.mpr hn
      have hne : ArithmeticFunction.cardFactors n ≠ 1 := fun h ↦
        hc (ArithmeticFunction.cardFactors_eq_one_iff_prime.mp h)
      have hlo : 2 ≤ ArithmeticFunction.cardFactors n :=
        Nat.succ_le_of_lt (lt_of_le_of_ne (Nat.succ_le_of_lt hpos) hne.symm)
      have hhi : ArithmeticFunction.cardFactors n < 3 := heq ▸ Nat.lt_of_not_ge hcard
      exact Nat.le_antisymm (Nat.lt_succ_iff.mp hhi) hlo
    obtain ⟨p, q, hp, hq, hpq, hprod⟩ :=
      NumberTheory.exists_ordered_prime_pair_of_cardFactors_two hn hk
    rcases hpq.eq_or_lt with heq | hlt
    · subst q
      have hnot := (Nat.squarefree_iff_prime_squarefree.mp hsf) p hp
      exact False.elim (hnot (hprod.symm ▸ dvd_rfl))
    · exact
        exists_prime_reject_03_semiprime_5551 hn ho hp hq hlt hprod hGRH hL (by linarith only [hU])

/-- Under GRH, each nonuniform odd composite with logarithm in `[8, 55.51]`
has a 0.30 rejecting prime, by the square-divisor and squarefree bounds. -/
theorem exists_prime_reject_03_nonuniform_5551 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hu : ¬UniformKorseltTriple n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (8 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 5551 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  by_cases hsq : ∃ p : ℕ, p.Prime ∧ p ^ 2 ∣ n
  · obtain ⟨p, hp, hd⟩ := hsq
    exact exists_prime_reject_03_square_8_to_805 hn ho hp hd hGRH.riemann hL (by linarith only [hU])
  · have hsf : Squarefree n :=
      Nat.squarefree_iff_prime_squarefree.mpr (fun p hp h ↦ hsq ⟨p, hp, (pow_two p).symm ▸ h⟩)
    exact exists_prime_reject_03_nonuniform_sf5551 hn ho hc hsf hu hGRH hL hU

end PseudoPrime.PrimeTestBounds.MillerRabin
