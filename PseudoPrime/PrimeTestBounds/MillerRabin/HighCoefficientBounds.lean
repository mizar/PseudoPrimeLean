/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.HighCoefficientRepeated
public import PseudoPrime.PrimeTestBounds.MillerRabin.HighCoefficientTriple
public import PseudoPrime.PrimeTestBounds.MillerRabin.FourNinthsHighWitness
public import PseudoPrime.PrimeTestBounds.MillerRabin.MixedTwoAdicLogBounds

/-! # High-range Miller–Rabin witness bounds -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, an odd composite with at least four prime factors counted
with multiplicity has a prime MR witness at most `(7 / 16) * log n ^ 2`.
The general factor-count witness already has coefficient at most `1 / 4`. -/
theorem highCoeff_manyFactors_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hk : 4 ≤ ArithmeticFunction.cardFactors n) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 16 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  obtain ⟨r, hr, hb, hf⟩ := exists_prime_witness_le_cardFactors_log_sq hn ho hc hGRH
  have hkR : (4 : ℝ) ≤ (ArithmeticFunction.cardFactors n : ℝ) := Nat.cast_le.mpr hk
  have hs : (16 : ℝ) ≤ (ArithmeticFunction.cardFactors n : ℝ) ^ 2 := by nlinarith only [hkR]
  have hp : (0 : ℝ) < (ArithmeticFunction.cardFactors n : ℝ) ^ 2 := by linarith only [hs]
  have hcoeff : (4 : ℝ) / (ArithmeticFunction.cardFactors n : ℝ) ^ 2 ≤ 7 / 16 := by
    apply (div_le_div_iff₀ hp (by norm_num only : (0 : ℝ) < 16)).mpr
    nlinarith only [hs]
  exact ⟨r, hr, hb.trans (mul_le_mul_of_nonneg_right hcoeff (sq_nonneg _)), hf⟩

/-- Under GRH, an odd composite with exactly two prime factors counted with
multiplicity and `log n ≥ 70000` has a prime MR witness at most
`(7 / 16) * log n ^ 2`. The ordered prime pair is either a square or consists
of distinct primes, and the corresponding high-range theorem applies. -/
theorem highCoeff_twoFactors_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (70000 : ℝ) ≤ Real.log n)
    (hcard : ArithmeticFunction.cardFactors n = 2) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 16 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  obtain ⟨p, q, hp, hq, hpq, hprod⟩ :=
    NumberTheory.exists_ordered_prime_pair_of_cardFactors_two hn hcard
  have hpdiv : p ∣ n := by
    rw [hprod]
    exact dvd_mul_right p q
  have hp2 : p ≠ 2 := ho.ne_two_of_dvd_nat hpdiv
  rcases hpq.eq_or_lt with heq | hlt
  · have hsquare : n = p ^ 2 := by rw [hprod, ← heq, pow_two]
    exact highCoeff_primePow_witness hn ho hp hp2 (by norm_num only : 2 ≤ 2) hsquare hGRH.riemann hL
  · exact highCoeff_semiprime_witness hn ho hc hp hq hlt hprod hGRH hL

/-- Under GRH, a squarefree odd `n > 1` with exactly three distinct prime
factors has a prime MR witness at most `(7 / 16) * log n ^ 2` for
`log n ≥ 70000`. Non-Korselt and mixed-valuation cases use the marked-factor
bound; the remaining case uses the index-four Gaussian comparison. -/
theorem highCoeff_squarefreeThree_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hsf : Squarefree n)
    (hcard : n.primeFactors.card = 3) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (70000 : ℝ) ≤ Real.log n) :
    ∃ s : ℕ,
      s.Prime ∧
        (s : ℝ) ≤ (7 / 16 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := by
  have hc : 3 ≤ n.primeFactors.card := hcard.ge
  by_cases hlocal :
    (∃ r ∈ n.primeFactors, ∃ s ∈ n.primeFactors, padicValNat 2 (s - 1) < padicValNat 2 (r - 1)) ∨
      ∃ r ∈ n.primeFactors, ¬r - 1 ∣ n - 1
  · obtain ⟨r, hr, hf, hb, _⟩ :=
      exists_leastWitness_le_local_factor_coefficient hn ho hc hlocal hGRH
    have hcoeff : (4 : ℝ) / ((n.primeFactors.card : ℝ) + 1) ^ 2 ≤ 7 / 16 := by
      rw [hcard]
      norm_num only [Nat.cast_ofNat]
    exact ⟨r, hr, hb.trans (mul_le_mul_of_nonneg_right hcoeff (sq_nonneg _)), hf⟩
  · have hK : ∀ p : ℕ, p.Prime → p ∣ n → p - 1 ∣ n - 1 := by
      intro p hp hpn
      by_contra hbad
      apply hlocal
      right
      exact ⟨p, Nat.mem_primeFactors.mpr ⟨hp, hpn, Nat.ne_zero_of_lt hn⟩, hbad⟩
    have hU :
      ∀ p q : ℕ,
        p.Prime → q.Prime → p ∣ n → q ∣ n → padicValNat 2 (p - 1) = padicValNat 2 (q - 1) := by
      intro p q hp hq hpn hqn
      by_contra hne
      have hpMem : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpn, Nat.ne_zero_of_lt hn⟩
      have hqMem : q ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hq, hqn, Nat.ne_zero_of_lt hn⟩
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact hlocal (Or.inl ⟨q, hqMem, p, hpMem, hlt⟩)
      · exact hlocal (Or.inl ⟨p, hpMem, q, hqMem, hgt⟩)
    obtain ⟨p, q, r, hpq, hpr, hqr, hset⟩ := Finset.card_eq_three.mp hcard
    have hpMem : p ∈ n.primeFactors := hset ▸ Finset.mem_insert_self p _
    have hqMem : q ∈ n.primeFactors := hset ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self q _)
    have hrMem : r ∈ n.primeFactors :=
      hset ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self r))
    have hp := (Nat.mem_primeFactors.mp hpMem).1
    have hq := (Nat.mem_primeFactors.mp hqMem).1
    have hr := (Nat.mem_primeFactors.mp hrMem).1
    have hpn := (Nat.mem_primeFactors.mp hpMem).2.1
    have hqn := (Nat.mem_primeFactors.mp hqMem).2.1
    have hrn := (Nat.mem_primeFactors.mp hrMem).2.1
    have hprod := (Nat.prod_primeFactors_of_squarefree hsf).symm
    rw [hset] at hprod
    have hnprod : n = p * q * r := by
      simpa only [Finset.prod_insert, Finset.prod_singleton, Finset.mem_insert,
        Finset.mem_singleton, hpq, hpr, hqr, or_self, not_false_eq_true, mul_assoc] using hprod
    exact
      highCoeff_threeKorselt_witness hp hq hr (hp.odd_of_ne_two (ho.ne_two_of_dvd_nat hpn))
        (hq.odd_of_ne_two (ho.ne_two_of_dvd_nat hqn)) (hr.odd_of_ne_two (ho.ne_two_of_dvd_nat hrn))
        hpq hpr hqr hnprod (hK p hp hpn) (hK q hq hqn) (hK r hr hrn) (hU p q hp hq hpn hqn)
        (hU p r hp hr hpn hrn) hGRH hL

/-- Under GRH, an odd composite with exactly three prime factors counted
with multiplicity and `log n ≥ 70000` has a prime MR witness at most
`(7 / 16) * log n ^ 2`. Repeated list entries give a `p ^ 2 * q` branch;
otherwise the factor list is squarefree with three distinct elements. -/
theorem highCoeff_threeFactors_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (70000 : ℝ) ≤ Real.log n)
    (hcard : ArithmeticFunction.cardFactors n = 3) :
    ∃ s : ℕ,
      s.Prime ∧
        (s : ℝ) ≤ (7 / 16 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := by
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
    exact highCoeff_squareTimesPrime_witness hn ho hc hp hr hn' hGRH hL
  by_cases hpr : p = r
  · subst r
    have hn' : n = p ^ 2 * q := by
      simpa only [pow_two, mul_assoc, mul_comm, mul_left_comm] using hnprod
    exact highCoeff_squareTimesPrime_witness hn ho hc hp hq hn' hGRH hL
  by_cases hqr : q = r
  · subst r
    have hn' : n = q ^ 2 * p := by
      simpa only [pow_two, mul_assoc, mul_comm, mul_left_comm] using hnprod
    exact highCoeff_squareTimesPrime_witness hn ho hc hq hp hn' hGRH hL
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
  exact highCoeff_squarefreeThree_witness hn ho hsf hdistinct hGRH hL

/-- Under GRH, every odd composite `n > 1` with `log n ≥ 70000` has a
prime Miller–Rabin witness at most `(7 / 16) * log n ^ 2`. Classify the
prime factors counted with multiplicity into two, three, or at least four. -/
theorem highCoeff_prime_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (70000 : ℝ) ≤ Real.log n) :
    ∃ s : ℕ,
      s.Prime ∧
        (s : ℝ) ≤ (7 / 16 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := by
  by_cases h4 : 4 ≤ ArithmeticFunction.cardFactors n
  · exact highCoeff_manyFactors_witness hn ho hc hGRH h4
  have hkpos := ArithmeticFunction.cardFactors_pos_iff_one_lt.mpr hn
  have hkne : ArithmeticFunction.cardFactors n ≠ 1 := fun h ↦
    hc (ArithmeticFunction.cardFactors_eq_one_iff_prime.mp h)
  have hk2 : 2 ≤ ArithmeticFunction.cardFactors n :=
    Nat.succ_le_of_lt (lt_of_le_of_ne (Nat.succ_le_of_lt hkpos) hkne.symm)
  by_cases h3 : ArithmeticFunction.cardFactors n = 3
  · exact highCoeff_threeFactors_witness hn ho hc hGRH hL h3
  have hle3 : ArithmeticFunction.cardFactors n ≤ 3 := Nat.lt_succ_iff.mp (Nat.lt_of_not_ge h4)
  have hle2 : ArithmeticFunction.cardFactors n ≤ 2 := Nat.lt_succ_iff.mp (lt_of_le_of_ne hle3 h3)
  exact highCoeff_twoFactors_witness hn ho hc hGRH hL (le_antisymm hle2 hk2)

/-- Under the same high-range hypotheses, the least prime Miller–Rabin witness
also satisfies the coefficient `7 / 16` bound. Minimize the rejecting-prime
predicate using the preceding existence theorem. -/
theorem highCoeff_least_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (70000 : ℝ) ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (7 / 16 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  exact exists_least_prime_reject_of_exists_prime_reject (highCoeff_prime_witness hn ho hc hGRH hL)

end PseudoPrime.PrimeTestBounds.MillerRabin
