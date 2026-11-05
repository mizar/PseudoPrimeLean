/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.MeanAllFactors
public import PseudoPrime.PrimeTestBounds.MillerRabin.MeanShortTriple
public import PseudoPrime.PrimeTestBounds.MillerRabin.ReducedContourWitness

/-! # All-factor fixed witness from the short mean-counting bridge -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, distinct semiprimes in the short interval have a rejecting prime below
coefficient `1057 / 2500`; split at the short mean-counting radius. -/
theorem short_distinct_witness {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (80000 : ℝ) ≤ Real.log n)
    (hLU : Real.log n ≤ 200000000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (1057 / 2500 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hdiv : q ∣ n := by
    rw [hprod]; exact dvd_mul_left q p
  have hq2 : q ≠ 2 := ho.ne_two_of_dvd_nat hdiv
  by_cases hsmall : Real.log q ≤ (3251 / 5000 : ℝ) * Real.log n
  · have hbad : ¬q - 1 ∣ n - 1 := by
      rw [hprod]
      exact NumberTheory.not_sub_one_dvd_prime_mul_sub_one_of_lt hp hq hpq
    obtain ⟨r, hr, hb, hf⟩ :=
      exists_prime_witness_le_nonKorselt_factor_log_sq hn ho hq hdiv hbad hGRH
    have hsq := pow_le_pow_left₀ (Real.log_natCast_nonneg q) hsmall 2
    have hc : (3251 / 5000 : ℝ) ^ 2 ≤ 1057 / 2500 := by norm_num only
    have hcoeff := mul_le_mul_of_nonneg_right hc (sq_nonneg (Real.log n))
    have he : ((3251 / 5000 : ℝ) * Real.log n) ^ 2 = (3251 / 5000 : ℝ) ^ 2 * (Real.log n) ^ 2 :=
      mul_pow _ _ 2
    exact ⟨r, hr, hb.trans (hsq.trans (he.le.trans hcoeff)), hf⟩
  · exact
      large_cofactor_witness_04228 hGRH.riemann hn ho hp.one_lt hq hq2 hprod hL hLU
        (lt_of_not_ge hsmall)


/-- Under GRH, odd composites with at least four factors satisfy the coefficient
`1057 / 2500` bound by the general multiplicity estimate. -/
theorem short_many_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hk : 4 ≤ ArithmeticFunction.cardFactors n) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (1057 / 2500 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  obtain ⟨r, hr, hb, hf⟩ := exists_prime_witness_le_cardFactors_log_sq hn ho hc hGRH
  have hkR : (4 : ℝ) ≤ (ArithmeticFunction.cardFactors n : ℝ) := Nat.cast_le.mpr hk
  have hs : (16 : ℝ) ≤ (ArithmeticFunction.cardFactors n : ℝ) ^ 2 := by nlinarith only [hkR]
  have hp : (0 : ℝ) < (ArithmeticFunction.cardFactors n : ℝ) ^ 2 := by linarith only [hs]
  have hcoeff : (4 : ℝ) / (ArithmeticFunction.cardFactors n : ℝ) ^ 2 ≤ 1057 / 2500 := by
    apply (div_le_div_iff₀ hp (by norm_num only : (0 : ℝ) < 2500)).mpr
    nlinarith only [hs]
  exact ⟨r, hr, hb.trans (mul_le_mul_of_nonneg_right hcoeff (sq_nonneg _)), hf⟩


/-- Under GRH, the two-factor case satisfies the short mean bridge bound.
Separate a prime square from distinct semiprimes. -/
theorem short_two_witness {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (80000 : ℝ) ≤ Real.log n)
    (hLU : Real.log n ≤ 200000000) (hcard : ArithmeticFunction.cardFactors n = 2) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (1057 / 2500 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  obtain ⟨p, q, hp, hq, hpq, hprod⟩ :=
    NumberTheory.exists_ordered_prime_pair_of_cardFactors_two hn hcard
  have hpdiv : p ∣ n := by
    rw [hprod]
    exact dvd_mul_right p q
  have hp2 : p ≠ 2 := ho.ne_two_of_dvd_nat hpdiv
  rcases hpq.eq_or_lt with heq | hlt
  · have hsquare : n = p ^ 2 := by rw [hprod, ← heq, pow_two]
    have hdiv : p ^ 2 ∣ n := hsquare.symm ▸ dvd_refl (p ^ 2)
    have hlower : Real.log n / 3 ≤ Real.log (p ^ 2 : ℕ) := by
      rw [← hsquare]
      linarith only [hL]
    have hupper : Real.log (p ^ 2 : ℕ) ≤ Real.log n := by rw [← hsquare]
    exact
      primePow_witness_04228 hn ho hp hp2 (by norm_num only : 2 ≤ 2) hdiv hGRH.riemann hL
        hlower hupper
  · exact short_distinct_witness hn ho hp hq hlt hprod hGRH hL hLU


/-- Under GRH, the three-factor case satisfies the short mean bridge bound.
Separate repeated factors from squarefree triples. -/
theorem short_three_witness {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (80000 : ℝ) ≤ Real.log n)
    (hLU : Real.log n ≤ 200000000) (hcard : ArithmeticFunction.cardFactors n = 3) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (1057 / 2500 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hl : n.primeFactorsList.length = 3 := by
    simpa only [ArithmeticFunction.cardFactors_apply] using hcard
  obtain ⟨p, q, r, hlist⟩ := List.length_eq_three.mp hl
  have hp : p.Prime :=
    Nat.prime_of_mem_primeFactorsList
      (by
        rw [hlist]; exact List.mem_cons_self)
  have hq : q.Prime :=
    Nat.prime_of_mem_primeFactorsList
      (by
        rw [hlist]; exact List.mem_cons_of_mem _ List.mem_cons_self)
  have hr : r.Prime :=
    Nat.prime_of_mem_primeFactorsList
      (by
        rw [hlist]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have hprod := Nat.prod_primeFactorsList (Nat.ne_zero_of_lt hn)
  rw [hlist] at hprod
  simp only [List.prod_cons, List.prod_nil, mul_one] at hprod
  have hnprod : n = p * q * r := by simpa only [mul_assoc] using hprod.symm
  by_cases hpq : p = q
  · subst q
    have hn' : n = p ^ 2 * r := by simpa only [pow_two] using hnprod
    exact squarePrime_witness_04228 hn ho hp hr hn' hGRH.riemann hL hLU
  by_cases hpr : p = r
  · subst r
    have hn' : n = p ^ 2 * q := by
      simpa only [pow_two, mul_assoc, mul_comm, mul_left_comm] using hnprod
    exact squarePrime_witness_04228 hn ho hp hq hn' hGRH.riemann hL hLU
  by_cases hqr : q = r
  · subst r
    have hn' : n = q ^ 2 * p := by
      simpa only [pow_two, mul_assoc, mul_comm, mul_left_comm] using hnprod
    exact squarePrime_witness_04228 hn ho hq hp hn' hGRH.riemann hL hLU
  have hnodup : n.primeFactorsList.Nodup := by
    rw [hlist]
    simp only [List.nodup_cons, List.nodup_nil, List.mem_cons, List.not_mem_nil, or_false, not_or,
      not_false_eq_true, and_true]
    exact ⟨⟨hpq, hpr⟩, hqr⟩
  have hsf : Squarefree n :=
    (Nat.squarefree_iff_nodup_primeFactorsList (Nat.ne_zero_of_lt hn)).2 hnodup
  have hdistinct : n.primeFactors.card = 3 := by
    change n.primeFactorsList.toFinset.card = 3
    rw [List.toFinset_card_of_nodup hnodup, hl]
  exact squarefreeThree_witness_04228 hn ho hsf hdistinct hGRH hL


/-- Under GRH, every odd composite in the short interval satisfies coefficient
`1057 / 2500`; classify its prime factors by multiplicity. -/
theorem short_finite_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (80000 : ℝ) ≤ Real.log n)
    (hLU : Real.log n ≤ 200000000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (1057 / 2500 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  by_cases h4 : 4 ≤ ArithmeticFunction.cardFactors n
  · exact short_many_witness hn ho hc hGRH h4
  have hkpos := ArithmeticFunction.cardFactors_pos_iff_one_lt.mpr hn
  have hkne : ArithmeticFunction.cardFactors n ≠ 1 := fun h ↦
    hc (ArithmeticFunction.cardFactors_eq_one_iff_prime.mp h)
  have hk2 : 2 ≤ ArithmeticFunction.cardFactors n :=
    Nat.succ_le_of_lt (lt_of_le_of_ne (Nat.succ_le_of_lt hkpos) hkne.symm)
  by_cases h3 : ArithmeticFunction.cardFactors n = 3
  · exact short_three_witness hn ho hGRH hL hLU h3
  have hle3 : ArithmeticFunction.cardFactors n ≤ 3 := Nat.lt_succ_iff.mp (Nat.lt_of_not_ge h4)
  have hle2 : ArithmeticFunction.cardFactors n ≤ 2 := Nat.lt_succ_iff.mp (lt_of_le_of_ne hle3 h3)
  exact short_two_witness hn ho hGRH hL hLU (le_antisymm hle2 hk2)

/-- Under GRH, every odd composite with `log n ≥ 80000` has a rejecting prime
at most `(1057 / 2500) * log n ^ 2`. The short mean-counting interval joins
the reduced-contour coefficient `39 / 100` beyond its entrance. -/
theorem prime_witness_04228 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (80000 : ℝ) ≤ Real.log n) :
    ∃ r : ℕ, r.Prime ∧
      (r : ℝ) ≤ (1057 / 2500 : ℝ) * (Real.log n) ^ 2 ∧
      ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  by_cases hsmall : Real.log n ≤ 200000000
  · exact short_finite_witness hn ho hc hGRH hL hsmall
  · have hlarge : (200000000 : ℝ) ≤ Real.log n := (lt_of_not_ge hsmall).le
    obtain ⟨r, hr, hb, hf⟩ := prime_witness_reduced039 hn ho hc hGRH hlarge
    have hcoeff : (39 / 100 : ℝ) ≤ 1057 / 2500 := by norm_num only
    exact ⟨r, hr, hb.trans (mul_le_mul_of_nonneg_right hcoeff (sq_nonneg _)), hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
