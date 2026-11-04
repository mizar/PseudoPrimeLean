/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.MeanRepeatedWitness
public import PseudoPrime.PrimeTestBounds.MillerRabin.MeanTripleBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.HighFactorialBounds

/-! # Fixed-coefficient witnesses for all factor structures -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, an odd product of distinct primes with `80000 ≤ log n ≤ 4 * 10 ^ 10`
has a rejecting prime within the coefficient `427 / 1000` bound. Split on the larger
prime's logarithmic size and apply either the local factor bound or mean counting.
This covers distinct semiprimes in the finite high-scale range. -/
theorem distinct_semiprime_witness_427 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (80000 : ℝ) ≤ Real.log n)
    (hLU : Real.log n ≤ 40000000000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (427 / 1000 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hdiv : q ∣ n := by
    rw [hprod]; exact dvd_mul_left q p
  have hq2 : q ≠ 2 := ho.ne_two_of_dvd_nat hdiv
  by_cases hsmall : Real.log q ≤ (13069 / 20000 : ℝ) * Real.log n
  · have hbad : ¬q - 1 ∣ n - 1 := by
      rw [hprod]
      exact NumberTheory.not_sub_one_dvd_prime_mul_sub_one_of_lt hp hq hpq
    obtain ⟨r, hr, hb, hf⟩ :=
      exists_prime_witness_le_nonKorselt_factor_log_sq hn ho hq hdiv hbad hGRH
    have hsq := pow_le_pow_left₀ (Real.log_natCast_nonneg q) hsmall 2
    have hc : (13069 / 20000 : ℝ) ^ 2 ≤ 427 / 1000 := by norm_num only
    have hcoeff := mul_le_mul_of_nonneg_right hc (sq_nonneg (Real.log n))
    have he : ((13069 / 20000 : ℝ) * Real.log n) ^ 2 = (13069 / 20000 : ℝ) ^ 2 * (Real.log n) ^ 2 :=
      mul_pow _ _ 2
    exact ⟨r, hr, hb.trans (hsq.trans (he.le.trans hcoeff)), hf⟩
  · exact
      large_cofactor_witness_427 hGRH.riemann hn ho hp.one_lt hq hq2 hprod hL hLU
        (lt_of_not_ge hsmall)

/-- Under GRH, a squarefree odd input with three distinct prime factors and
`log n ≥ 80000` has a rejecting prime within the coefficient `427 / 1000` bound.
Apply the fixed-radius Gaussian and local-factor theorem, then round the coefficient.
This supplies the squarefree three-factor case. -/
theorem squarefreeThree_witness_427 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hsf : Squarefree n)
    (hcard : n.primeFactors.card = 3) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (80000 : ℝ) ≤ Real.log n) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (427 / 1000 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  obtain ⟨r, hr, hb, hf⟩ := mean_squarefreeThree_witness hn ho hsf hcard hGRH hL
  have hc : (13069 / 20000 : ℝ) ^ 2 ≤ 427 / 1000 := by norm_num only
  exact ⟨r, hr, hb.trans (mul_le_mul_of_nonneg_right hc (sq_nonneg _)), hf⟩

/-- Under GRH, an odd composite with at least four prime factors counted with multiplicity
has a rejecting prime within the coefficient `427 / 1000` bound. The general factor-count
bound has coefficient at most `1 / 4`. This covers the many-factor case. -/
theorem manyFactors_witness_427 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hk : 4 ≤ ArithmeticFunction.cardFactors n) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (427 / 1000 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  obtain ⟨r, hr, hb, hf⟩ := exists_prime_witness_le_cardFactors_log_sq hn ho hc hGRH
  have hkR : (4 : ℝ) ≤ (ArithmeticFunction.cardFactors n : ℝ) := Nat.cast_le.mpr hk
  have hs : (16 : ℝ) ≤ (ArithmeticFunction.cardFactors n : ℝ) ^ 2 := by nlinarith only [hkR]
  have hp : (0 : ℝ) < (ArithmeticFunction.cardFactors n : ℝ) ^ 2 := by linarith only [hs]
  have hcoeff : (4 : ℝ) / (ArithmeticFunction.cardFactors n : ℝ) ^ 2 ≤ 427 / 1000 := by
    apply (div_le_div_iff₀ hp (by norm_num only : (0 : ℝ) < 1000)).mpr
    nlinarith only [hs]
  exact ⟨r, hr, hb.trans (mul_le_mul_of_nonneg_right hcoeff (sq_nonneg _)), hf⟩

/-- Under GRH, an odd input with two prime factors counted with multiplicity and
`80000 ≤ log n ≤ 4 * 10 ^ 10` has a rejecting prime within the coefficient
`427 / 1000` bound. The ordered prime pair is either a square or consists of distinct
primes, and the corresponding witness theorem applies. -/
theorem twoFactors_witness_427 {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (80000 : ℝ) ≤ Real.log n)
    (hLU : Real.log n ≤ 40000000000) (hcard : ArithmeticFunction.cardFactors n = 2) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (427 / 1000 : ℝ) * (Real.log n) ^ 2 ∧
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
      primePow_divisor_witness_427 hn ho hp hp2 (by norm_num only : 2 ≤ 2) hdiv hGRH.riemann hL
        hlower hupper
  · exact distinct_semiprime_witness_427 hn ho hp hq hlt hprod hGRH hL hLU

/-- Under GRH, an odd input with three prime factors counted with multiplicity and
`80000 ≤ log n ≤ 4 * 10 ^ 10` has a rejecting prime within the coefficient
`427 / 1000` bound. Split the factor list into repeated and squarefree cases and
apply the corresponding witness theorem. -/
theorem threeFactors_witness_427 {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (80000 : ℝ) ≤ Real.log n)
    (hLU : Real.log n ≤ 40000000000) (hcard : ArithmeticFunction.cardFactors n = 3) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (427 / 1000 : ℝ) * (Real.log n) ^ 2 ∧
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
    exact squareTimesPrime_witness_427 hn ho hp hr hn' hGRH.riemann hL hLU
  by_cases hpr : p = r
  · subst r
    have hn' : n = p ^ 2 * q := by
      simpa only [pow_two, mul_assoc, mul_comm, mul_left_comm] using hnprod
    exact squareTimesPrime_witness_427 hn ho hp hq hn' hGRH.riemann hL hLU
  by_cases hqr : q = r
  · subst r
    have hn' : n = q ^ 2 * p := by
      simpa only [pow_two, mul_assoc, mul_comm, mul_left_comm] using hnprod
    exact squareTimesPrime_witness_427 hn ho hq hp hn' hGRH.riemann hL hLU
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
  exact squarefreeThree_witness_427 hn ho hsf hdistinct hGRH hL

/-- Under GRH, every odd composite with `80000 ≤ log n ≤ 4 * 10 ^ 10` has a
rejecting prime at most `(427 / 1000) * log n ^ 2`. Classify the prime factors by
multiplicity and apply the two-, three-, and many-factor bounds. This joins all factor
structures in the finite high-scale range. -/
theorem prime_witness_427_finite {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (80000 : ℝ) ≤ Real.log n)
    (hLU : Real.log n ≤ 40000000000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (427 / 1000 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  by_cases h4 : 4 ≤ ArithmeticFunction.cardFactors n
  · exact manyFactors_witness_427 hn ho hc hGRH h4
  have hkpos := ArithmeticFunction.cardFactors_pos_iff_one_lt.mpr hn
  have hkne : ArithmeticFunction.cardFactors n ≠ 1 := fun h ↦
    hc (ArithmeticFunction.cardFactors_eq_one_iff_prime.mp h)
  have hk2 : 2 ≤ ArithmeticFunction.cardFactors n :=
    Nat.succ_le_of_lt (lt_of_le_of_ne (Nat.succ_le_of_lt hkpos) hkne.symm)
  by_cases h3 : ArithmeticFunction.cardFactors n = 3
  · exact threeFactors_witness_427 hn ho hGRH hL hLU h3
  have hle3 : ArithmeticFunction.cardFactors n ≤ 3 := Nat.lt_succ_iff.mp (Nat.lt_of_not_ge h4)
  have hle2 : ArithmeticFunction.cardFactors n ≤ 2 := Nat.lt_succ_iff.mp (lt_of_le_of_ne hle3 h3)
  exact twoFactors_witness_427 hn ho hGRH hL hLU (le_antisymm hle2 hk2)

/-- Under GRH, every odd composite with `log n ≥ 80000` has a rejecting prime at most
`(427 / 1000) * log n ^ 2`. The finite interval uses the average-logarithm bound, and
the existing triangular profile supplies a smaller coefficient beyond `4 * 10 ^ 10`.
This gives the fixed-coefficient witness on its entire advertised range. -/
theorem prime_witness_427 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (80000 : ℝ) ≤ Real.log n) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (427 / 1000 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  by_cases hsmall : Real.log n ≤ 40000000000
  · exact prime_witness_427_finite hn ho hc hGRH hL hsmall
  · have hlarge : (40000000000 : ℝ) ≤ Real.log n := (lt_of_not_ge hsmall).le
    have ht : triangularP04145.T ≤ Real.log n := by
      change (40000000000 : ℝ) ≤ Real.log n
      exact hlarge
    obtain ⟨r, hr, hb, hf⟩ := exists_prime_triangularProfile triangularP04145 hn ho hc hGRH ht
    have hcoeff : triangularP04145.C ≤ (427 / 1000 : ℝ) := by
      change (4145 / 10000 : ℝ) ≤ 427 / 1000
      norm_num only
    exact ⟨r, hr, hb.trans (mul_le_mul_of_nonneg_right hcoeff (sq_nonneg _)), hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
