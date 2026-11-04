/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.HighVariableRepeated

/-! # Variable paired-coefficient bounds for all odd composites -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, an odd composite with at least four prime factors counted with multiplicity and
`log n ≥ 70000` has a rejecting prime within the paired bound. The existing factor-count
coefficient is at most `1 / 4`, below the square of the variable coefficient. -/
theorem paired_manyFactors_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (70000 : ℝ) ≤ Real.log n)
    (hk : 4 ≤ ArithmeticFunction.cardFactors n) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (pairedAlpha (2 * Real.log (Real.log n))) ^ 2 * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  obtain ⟨r, hr, hb, hf⟩ := exists_prime_witness_le_cardFactors_log_sq hn ho hc hGRH
  have hkR : (4 : ℝ) ≤ (ArithmeticFunction.cardFactors n : ℝ) := Nat.cast_le.mpr hk
  have hs : (16 : ℝ) ≤ (ArithmeticFunction.cardFactors n : ℝ) ^ 2 := by nlinarith only [hkR]
  have hp : (0 : ℝ) < (ArithmeticFunction.cardFactors n : ℝ) ^ 2 := by linarith only [hs]
  have hcoeff : (4 : ℝ) / (ArithmeticFunction.cardFactors n : ℝ) ^ 2 ≤ 1 / 4 := by
    apply (div_le_div_iff₀ hp (by norm_num only : (0 : ℝ) < 4)).mpr
    nlinarith only [hs]
  have hα := pairedAlpha_ge_653 (high_log_twice_ge_22 hL)
  have hαsq : (1 / 4 : ℝ) ≤ (pairedAlpha (2 * Real.log (Real.log n))) ^ 2 := by
    nlinarith only [hα, sq_nonneg (pairedAlpha (2 * Real.log (Real.log n)) - 653 / 1000)]
  exact ⟨r, hr, hb.trans (mul_le_mul_of_nonneg_right (hcoeff.trans hαsq) (sq_nonneg _)), hf⟩

/-- Under GRH, an odd composite with exactly two prime factors counted with multiplicity and
`log n ≥ 70000` has a rejecting prime within the paired bound. The square case uses prime-power
counting; the distinct-factor case uses the variable semiprime estimate. -/
theorem paired_twoFactors_witness {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (70000 : ℝ) ≤ Real.log n)
    (hcard : ArithmeticFunction.cardFactors n = 2) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (pairedAlpha (2 * Real.log (Real.log n))) ^ 2 * (Real.log n) ^ 2 ∧
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
      paired_primePow_divisor hn ho hp hp2 (by norm_num only : 2 ≤ 2) hdiv hGRH.riemann hL hlower
        hupper
  · exact distinct_semiprime_witness_paired hn ho hp hq hlt hprod hGRH hL

/-- Under GRH, an odd composite with exactly three prime factors counted with multiplicity and
`log n ≥ 70000` has a rejecting prime within the paired bound. Repeated factors use the `p ^ 2 * q`
branch; distinct factors use the squarefree Gaussian and local-factor branches. -/
theorem paired_threeFactors_witness {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (70000 : ℝ) ≤ Real.log n)
    (hcard : ArithmeticFunction.cardFactors n = 3) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (pairedAlpha (2 * Real.log (Real.log n))) ^ 2 * (Real.log n) ^ 2 ∧
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
    exact paired_squareTimesPrime_witness hn ho hp hr hn' hGRH hL
  by_cases hpr : p = r
  · subst r
    have hn' : n = p ^ 2 * q := by
      simpa only [pow_two, mul_assoc, mul_comm, mul_left_comm] using hnprod
    exact paired_squareTimesPrime_witness hn ho hp hq hn' hGRH hL
  by_cases hqr : q = r
  · subst r
    have hn' : n = q ^ 2 * p := by
      simpa only [pow_two, mul_assoc, mul_comm, mul_left_comm] using hnprod
    exact paired_squareTimesPrime_witness hn ho hq hp hn' hGRH hL
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
  exact paired_squarefreeThree_witness hn ho hsf hdistinct hGRH hL

/-- Under GRH, every odd composite `n` with `log n ≥ 70000` has a prime Miller–Rabin witness
within the squared variable paired coefficient. The proof classifies prime factors counted with
multiplicity and connects the counting and Gaussian branches. -/
theorem paired_prime_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (70000 : ℝ) ≤ Real.log n) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (pairedAlpha (2 * Real.log (Real.log n))) ^ 2 * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  by_cases h4 : 4 ≤ ArithmeticFunction.cardFactors n
  · exact paired_manyFactors_witness hn ho hc hGRH hL h4
  have hkpos := ArithmeticFunction.cardFactors_pos_iff_one_lt.mpr hn
  have hkne : ArithmeticFunction.cardFactors n ≠ 1 := fun h ↦
    hc (ArithmeticFunction.cardFactors_eq_one_iff_prime.mp h)
  have hk2 : 2 ≤ ArithmeticFunction.cardFactors n :=
    Nat.succ_le_of_lt (lt_of_le_of_ne (Nat.succ_le_of_lt hkpos) hkne.symm)
  by_cases h3 : ArithmeticFunction.cardFactors n = 3
  · exact paired_threeFactors_witness hn ho hGRH hL h3
  have hle3 : ArithmeticFunction.cardFactors n ≤ 3 := Nat.lt_succ_iff.mp (Nat.lt_of_not_ge h4)
  have hle2 : ArithmeticFunction.cardFactors n ≤ 2 := Nat.lt_succ_iff.mp (lt_of_le_of_ne hle3 h3)
  exact paired_twoFactors_witness hn ho hGRH hL (le_antisymm hle2 hk2)

end PseudoPrime.PrimeTestBounds.MillerRabin
