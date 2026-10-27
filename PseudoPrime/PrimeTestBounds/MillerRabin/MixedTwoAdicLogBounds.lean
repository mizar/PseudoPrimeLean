/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.MarkedFactorLogBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.TotalFactorWitnessBounds

/-! # An improved prime-factor coefficient in the mixed-two-adic branch -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, prime factors s,r with unequal predecessor two-adic valuations
give a prime MR witness at most log(r)^2 at the larger-valuation factor r.
Every strong pass lies in the proper local half-power kernel modulo r.
No squarefree or Korselt divisibility hypothesis is required. -/
theorem exists_prime_witness_le_larger_twoAdic_log_sq {n r s : ℕ} (hn : 1 < n) (ho : Odd n)
    (hr : r.Prime) (hs : s.Prime) (hrn : r ∣ n) (hsn : s ∣ n)
    (hv : padicValNat 2 (s - 1) < padicValNat 2 (r - 1))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ q : ℕ,
      q.Prime ∧ (q : ℝ) ≤ (Real.log r) ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) := by
  have hrOdd := hr.odd_of_ne_two (ho.ne_two_of_dvd_nat hrn)
  have hsOdd := hs.odd_of_ne_two (ho.ne_two_of_dvd_nat hsn)
  have hr3 : r ≠ 3 := by
    intro he
    have hsmall : padicValNat 2 (s - 1) < 1 := by
      simpa only [he, show (3 - 1 : ℕ) = 2 by decide, padicValNat.self (by decide : 1 < 2)] using hv
    exact (not_lt_of_ge (PrimeTest.odd_sub_canonical_decomp hs.one_lt hsOdd).1) hsmall
  have hr5 := hr.five_le_of_ne_two_of_ne_three (ho.ne_two_of_dvd_nat hrn) hr3
  let : Fact r.Prime := ⟨hr⟩
  let : Fact s.Prime := ⟨hs⟩
  let : NeZero r := ⟨hr.ne_zero⟩
  exact
    exists_prime_witness_le_local_log_sq hn ho hr5 hrn
      (powMonoidHom (r / 2) : (ZMod r)ˣ →* (ZMod r)ˣ).ker
      (PrimeTest.local_half_powerKernel_ne_top hrOdd)
      (fun a ha ↦
        PrimeTest.strongMillerRabinPass_mem_local_half_kernel_of_twoAdic_lt hn ho hrOdd hsOdd hrn
          hsn hv ha)
      hGRH

/-- Under GRH, odd n>1 with at least three distinct prime factors and two
unequal predecessor two-adic valuations has a prime MR witness at most
4 log(n)^2/(omega(n)+1)^2. Select either the marked larger-valuation prime
or a complementary prime pair. Squarefreeness and Korselt conditions are absent. -/
theorem exists_prime_witness_le_mixed_twoAdic_coefficient {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hc : 3 ≤ n.primeFactors.card)
    (hmix :
      ∃ r ∈ n.primeFactors, ∃ s ∈ n.primeFactors, padicValNat 2 (s - 1) < padicValNat 2 (r - 1))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ q : ℕ,
      q.Prime ∧
        (q : ℝ) ≤ (4 / ((n.primeFactors.card : ℝ) + 1) ^ 2) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) := by
  obtain ⟨r, hr, s, hs, hv⟩ := hmix
  have hlocal :=
    exists_prime_witness_le_larger_twoAdic_log_sq hn ho (Nat.prime_of_mem_primeFactors hr)
      (Nat.prime_of_mem_primeFactors hs) (Nat.dvd_of_mem_primeFactors hr)
      (Nat.dvd_of_mem_primeFactors hs) hv hGRH
  exact exists_prime_witness_le_marked_factor_coefficient hn ho hc hr hlocal hGRH

/-- Under the mixed-two-adic hypotheses, the least prime MR witness obeys
the improved omega(n)+1 coefficient. Minimize the full rejecting-prime
predicate after applying the pointwise witness theorem.
The minimum includes all prime bases, including two. -/
theorem exists_least_prime_witness_le_mixed_twoAdic_coefficient {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hc : 3 ≤ n.primeFactors.card)
    (hmix :
      ∃ r ∈ n.primeFactors, ∃ s ∈ n.primeFactors, padicValNat 2 (s - 1) < padicValNat 2 (r - 1))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ q : ℕ,
      q.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) ∧
        (q : ℝ) ≤ (4 / ((n.primeFactors.card : ℝ) + 1) ^ 2) * (Real.log n) ^ 2 ∧
        ∀ s : ℕ, s.Prime → ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) → q ≤ s := by
  obtain ⟨r, hr, s, hs, hv⟩ := hmix
  have hlocal :=
    exists_prime_witness_le_larger_twoAdic_log_sq hn ho (Nat.prime_of_mem_primeFactors hr)
      (Nat.prime_of_mem_primeFactors hs) (Nat.dvd_of_mem_primeFactors hr)
      (Nat.dvd_of_mem_primeFactors hs) hv hGRH
  exact exists_least_prime_witness_le_marked_factor_coefficient hn ho hc hr hlocal hGRH

/-- Under GRH and omega(n)≥3, either unequal predecessor two-adic valuations
or a failure of Korselt divisibility gives the improved least-prime coefficient.
Apply the corresponding closed local theorem; no local-witness hypothesis remains.
This combines the two marked-factor branches for downstream exponent bounds. -/
theorem exists_least_prime_witness_le_local_factor_coefficient {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hc : 3 ≤ n.primeFactors.card)
    (hlocal :
      (∃ r ∈ n.primeFactors, ∃ s ∈ n.primeFactors, padicValNat 2 (s - 1) < padicValNat 2 (r - 1)) ∨
        ∃ r ∈ n.primeFactors, ¬r - 1 ∣ n - 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ q : ℕ,
      q.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) ∧
        (q : ℝ) ≤ (4 / ((n.primeFactors.card : ℝ) + 1) ^ 2) * (Real.log n) ^ 2 ∧
        ∀ s : ℕ, s.Prime → ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) → q ≤ s := by
  rcases hlocal with hmix | hbad
  · exact exists_least_prime_witness_le_mixed_twoAdic_coefficient hn ho hc hmix hGRH
  · exact exists_least_prime_witness_le_nonKorselt_factor_coefficient hn ho hc hbad hGRH

/-- Under GRH with a mixed-two-adic or non-Korselt factor, the condition
omega(n)+1≥2 log(n)^(epsilon/2) gives a least-prime bound log(n)^(2-epsilon),
strictly below log(n)^2 for epsilon>0. Apply the shared real-power budget.
This is a pointwise structured-family result with no unspecified threshold. -/
theorem exists_least_prime_witness_le_log_power_of_local_factor {n : ℕ} {epsilon : ℝ} (hn : 1 < n)
    (ho : Odd n) (hc : 3 ≤ n.primeFactors.card)
    (hlocal :
      (∃ r ∈ n.primeFactors, ∃ s ∈ n.primeFactors, padicValNat 2 (s - 1) < padicValNat 2 (r - 1)) ∨
        ∃ r ∈ n.primeFactors, ¬r - 1 ∣ n - 1)
    (he : 0 < epsilon) (hk : 2 * (Real.log n) ^ (epsilon / 2) ≤ (n.primeFactors.card : ℝ) + 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ q : ℕ,
      q.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) ∧
        (q : ℝ) ≤ (Real.log n) ^ (2 - epsilon) ∧
        (q : ℝ) < (Real.log n) ^ 2 ∧
        ∀ s : ℕ, s.Prime → ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) → q ≤ s := by
  obtain ⟨q, hq, hf, hb, hleast⟩ :=
    exists_least_prime_witness_le_local_factor_coefficient hn ho hc hlocal hGRH
  have hn3 : 3 ≤ n := Nat.succ_le_of_lt (lt_of_le_of_ne hn (ho.ne_two_of_dvd_nat (dvd_refl n)).symm)
  have hl := Real.log_le_log (by norm_num only : (0 : ℝ) < 3) (Nat.cast_le.mpr hn3)
  have hL : 1 < Real.log n := by linarith only [hl, Real.log_three_gt_d9]
  have hbound := hb.trans (omega_coefficient_le_log_power (zero_lt_one.trans hL) hk)
  have hstrict : (Real.log n) ^ (2 - epsilon) < (Real.log n) ^ 2 := by
    simpa only [Real.rpow_two] using
      Real.rpow_lt_rpow_of_exponent_lt hL (show 2 - epsilon < (2 : ℝ) by linarith only [he])
  exact ⟨q, hq, hf, hbound, hbound.trans_lt hstrict, hleast⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
