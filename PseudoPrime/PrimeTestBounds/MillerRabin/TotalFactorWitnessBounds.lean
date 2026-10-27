/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimePairLogSquareBounds
public import PseudoPrime.NumberTheory.PrimeFactorLogMean

/-! # MR witness bounds using the total number of prime factors -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, any odd composite n greater than one has an actual prime MR
failing base at most 4 log(n)^2 / Omega(n)^2, counting factors with multiplicity.
Select the first two prime factors, apply the local product-modulus theorem,
and square the logarithmic mean bound. No additional lower cutoff is needed. -/
theorem exists_prime_witness_le_cardFactors_log_sq {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / (ArithmeticFunction.cardFactors n : ℝ) ^ 2) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hkpos := ArithmeticFunction.cardFactors_pos_iff_one_lt.mpr hn
  have hkne : ArithmeticFunction.cardFactors n ≠ 1 := fun h ↦
    hc (ArithmeticFunction.cardFactors_eq_one_iff_prime.mp h)
  have hk2 : 2 ≤ n.primeFactorsList.length :=
    Nat.succ_le_of_lt (lt_of_le_of_ne (Nat.succ_le_of_lt hkpos) hkne.symm)
  obtain ⟨p, q, hp, hq, hd, hm⟩ :=
    NumberTheory.exists_prime_pair_log_mean (Nat.zero_lt_of_lt hn) hk2
  obtain ⟨r, hr, hb, hf⟩ := exists_prime_witness_le_prime_pair_log_sq hn ho hp hq hd hGRH
  have hkR : (0 : ℝ) < ArithmeticFunction.cardFactors n := Nat.cast_pos.mpr hkpos
  have hlog :
    Real.log ((p * q : ℕ) : ℝ) ≤ 2 * Real.log n / (ArithmeticFunction.cardFactors n : ℝ) := by
    apply (le_div_iff₀ hkR).mpr
    simpa only [ArithmeticFunction.cardFactors_apply, mul_comm] using hm
  have hs := pow_le_pow_left₀ (Real.log_natCast_nonneg (p * q)) hlog 2
  have he :
    (2 * Real.log n / (ArithmeticFunction.cardFactors n : ℝ)) ^ 2 =
      (4 / (ArithmeticFunction.cardFactors n : ℝ) ^ 2) * (Real.log n) ^ 2 := by
    ring
  exact ⟨r, hr, hb.trans (hs.trans_eq he), hf⟩

/-- For positive L, k at least 2 L^(epsilon/2) converts the Omega coefficient
bound into L^(2-epsilon). Square the structural condition and use real-power
identities. Epsilon may be arbitrary; applications can restrict it to (0,2). -/
theorem omega_coefficient_le_log_power {L k epsilon : ℝ} (hL : 0 < L)
    (hk : 2 * L ^ (epsilon / 2) ≤ k) : (4 / k ^ 2) * L ^ 2 ≤ L ^ (2 - epsilon) := by
  have hepos := Real.rpow_pos_of_pos hL (epsilon / 2)
  have hkpos : 0 < k := (mul_pos (by norm_num only : (0 : ℝ) < 2) hepos).trans_le hk
  have hs := pow_le_pow_left₀ (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2) hepos.le) hk 2
  have he : (L ^ (epsilon / 2)) ^ (2 : ℕ) = L ^ epsilon := by
    rw [← Real.rpow_two, ← Real.rpow_mul hL.le]
    congr 1
    ring
  rw [mul_pow, he] at hs
  have hr : 4 / k ^ 2 ≤ 1 / L ^ epsilon := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hkpos) (Real.rpow_pos_of_pos hL epsilon)).mpr
    nlinarith only [hs]
  have hprod := mul_le_mul_of_nonneg_right hr (sq_nonneg L)
  have hident : (1 / L ^ epsilon) * L ^ 2 = L ^ (2 - epsilon) := by
    rw [Real.rpow_sub hL, Real.rpow_two]
    ring
  exact hprod.trans_eq hident

/-- Under GRH for an odd composite n greater than one, the structural
condition Omega(n) at least 2 log(n)^(epsilon/2) yields an actual prime MR
failing base at most log(n)^(2-epsilon). This is a pointwise structured-family
result, not a uniform exponent improvement for all composite inputs. -/
theorem exists_prime_witness_le_log_power_of_cardFactors {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hc : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {epsilon : ℝ}
    (hk : 2 * (Real.log n) ^ (epsilon / 2) ≤ (ArithmeticFunction.cardFactors n : ℝ)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (Real.log n) ^ (2 - epsilon) ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  obtain ⟨r, hr, hb, hf⟩ := exists_prime_witness_le_cardFactors_log_sq hn ho hc hGRH
  have hL := Real.log_pos (Nat.one_lt_cast.mpr hn : (1 : ℝ) < n)
  exact ⟨r, hr, hb.trans (omega_coefficient_le_log_power hL hk), hf⟩

/-- Under GRH, the least prime MR failing base obeys the total-factor bound.
Minimize the full prime-failure predicate after constructing one bounded base.
The minimum is taken over all prime bases, including two. -/
theorem exists_least_prime_witness_le_cardFactors_log_sq {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hc : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ (4 / (ArithmeticFunction.cardFactors n : ℝ) ^ 2) * (Real.log n) ^ 2 ∧
        ∀ r : ℕ, r.Prime → ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) → p ≤ r := by
  classical
  obtain ⟨p, hp, hb, hf⟩ := exists_prime_witness_le_cardFactors_log_sq hn ho hc hGRH
  have hex : ∃ r : ℕ, r.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := ⟨p, hp, hf⟩
  exact
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2,
      (Nat.cast_le.mpr (Nat.find_min' hex ⟨hp, hf⟩)).trans hb, fun r hr hf ↦
      Nat.find_min' hex ⟨hr, hf⟩⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
