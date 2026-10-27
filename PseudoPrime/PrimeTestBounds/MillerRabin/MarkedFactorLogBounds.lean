/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.MarkedPrimeFactorLogMean
public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimePairLogSquareBounds

/-! # A marked local MR witness or a complementary prime pair -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- If k>0 and k log(m)≤2 log(n), then log(m)^2≤4 log(n)^2/k²
for m≥1. Divide the linear logarithmic bound and square nonnegative terms.
This converts a selected local modulus into a prime-factor coefficient. -/
theorem log_sq_le_four_div_sq_of_weighted_mean {m n : ℕ} {k : ℝ} (hm : 1 ≤ m) (hk : 0 < k)
    (hmean : k * Real.log m ≤ 2 * Real.log n) :
    (Real.log m) ^ 2 ≤ (4 / k ^ 2) * (Real.log n) ^ 2 := by
  have hlog : Real.log m ≤ 2 * Real.log n / k :=
    (le_div_iff₀ hk).mpr (by simpa only [mul_comm] using hmean)
  have hs := pow_le_pow_left₀ (Real.log_nonneg (Nat.one_le_cast.mpr hm)) hlog 2
  have he : (2 * Real.log n / k) ^ 2 = (4 / k ^ 2) * (Real.log n) ^ 2 := by ring
  exact hs.trans_eq he

/-- Under GRH, a prime factor r with a local log(r)^2 MR witness bound
improves the global coefficient to 4/(omega(n)+1)^2 when omega(n)≥3.
Select r or a complementary prime pair by the marked logarithmic mean.
This generic transfer is shared by mixed-two-adic and non-Korselt branches. -/
theorem exists_prime_witness_le_marked_factor_coefficient {n r : ℕ} (hn : 1 < n) (ho : Odd n)
    (hc : 3 ≤ n.primeFactors.card) (hr : r ∈ n.primeFactors)
    (hlocal :
      ∃ q : ℕ,
        q.Prime ∧ (q : ℝ) ≤ (Real.log r) ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ q : ℕ,
      q.Prime ∧
        (q : ℝ) ≤ (4 / ((n.primeFactors.card : ℝ) + 1) ^ 2) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) := by
  have hrP := Nat.prime_of_mem_primeFactors hr
  have hk : (0 : ℝ) < (n.primeFactors.card : ℝ) + 1 :=
    add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) zero_lt_one
  rcases NumberTheory.marked_prime_or_pair_log_mean (Nat.zero_lt_of_lt hn) hr hc with hmean |
    ⟨p, q, hp, hq, _, hd, hmean⟩
  · obtain ⟨q, hq, hb, hf⟩ := hlocal
    exact ⟨q, hq, hb.trans (log_sq_le_four_div_sq_of_weighted_mean hrP.one_lt.le hk hmean), hf⟩
  · obtain ⟨r, hr, hb, hf⟩ := exists_prime_witness_le_prime_pair_log_sq hn ho hp hq hd hGRH
    have hm : 1 ≤ p * q := Nat.succ_le_of_lt (Nat.mul_pos hp.pos hq.pos)
    exact ⟨r, hr, hb.trans (log_sq_le_four_div_sq_of_weighted_mean hm hk hmean), hf⟩

/-- Under the marked-factor hypotheses, the least prime MR witness obeys
the coefficient 4/(omega(n)+1)^2. Minimize the full prime-rejection predicate.
This shared minimization avoids branch-specific existence choices. -/
theorem exists_least_prime_witness_le_marked_factor_coefficient {n r : ℕ} (hn : 1 < n) (ho : Odd n)
    (hc : 3 ≤ n.primeFactors.card) (hr : r ∈ n.primeFactors)
    (hlocal :
      ∃ q : ℕ,
        q.Prime ∧ (q : ℝ) ≤ (Real.log r) ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ q : ℕ,
      q.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) ∧
        (q : ℝ) ≤ (4 / ((n.primeFactors.card : ℝ) + 1) ^ 2) * (Real.log n) ^ 2 ∧
        ∀ s : ℕ, s.Prime → ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) → q ≤ s := by
  classical
  obtain ⟨q, hq, hb, hf⟩ :=
    exists_prime_witness_le_marked_factor_coefficient hn ho hc hr hlocal hGRH
  have hex : ∃ s : ℕ, s.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := ⟨q, hq, hf⟩
  exact
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2,
      (Nat.cast_le.mpr (Nat.find_min' hex ⟨hq, hf⟩)).trans hb, fun s hs hfail ↦
      Nat.find_min' hex ⟨hs, hfail⟩⟩

/-- Under GRH, a prime factor r with r-1 not dividing n-1 gives an MR
witness at most log(r)^2 for odd n>1. Its local ambient-power kernel
is proper. The factor r=3 is excluded by the parity of n-1.
This is the single-factor input for the non-Korselt coefficient improvement. -/
theorem exists_prime_witness_le_nonKorselt_factor_log_sq {n r : ℕ} (hn : 1 < n) (ho : Odd n)
    (hr : r.Prime) (hrn : r ∣ n) (hbad : ¬r - 1 ∣ n - 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ q : ℕ,
      q.Prime ∧ (q : ℝ) ≤ (Real.log r) ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) := by
  have hr3 : r ≠ 3 := by
    intro he
    apply hbad
    have ht : 2 ∣ n - 1 := even_iff_two_dvd.mp (Nat.Odd.sub_odd ho odd_one)
    simpa only [he, show (3 - 1 : ℕ) = 2 by decide] using ht
  have hr5 := hr.five_le_of_ne_two_of_ne_three (ho.ne_two_of_dvd_nat hrn) hr3
  let : Fact r.Prime := ⟨hr⟩
  let : NeZero r := ⟨hr.ne_zero⟩
  exact
    exists_prime_witness_le_local_log_sq hn ho hr5 hrn
      (powMonoidHom (n - 1) : (ZMod r)ˣ →* (ZMod r)ˣ).ker
      (PrimeTest.local_prime_powerKernel_ne_top_of_not_dvd hbad)
      (fun a ha ↦ PrimeTest.strongMillerRabinPass_mem_local_prime_powerKernel hn ho hrn ha) hGRH

/-- Under GRH, an odd n>1 with at least three distinct prime factors and
a factor violating Korselt divisibility has least prime MR witness at most
4 log(n)^2/(omega(n)+1)^2. Construct the local witness and apply marked-factor
selection and minimization. No squarefree hypothesis is required. -/
theorem exists_least_prime_witness_le_nonKorselt_factor_coefficient {n : ℕ} (hn : 1 < n)
    (ho : Odd n) (hc : 3 ≤ n.primeFactors.card) (hbad : ∃ r ∈ n.primeFactors, ¬r - 1 ∣ n - 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ q : ℕ,
      q.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) ∧
        (q : ℝ) ≤ (4 / ((n.primeFactors.card : ℝ) + 1) ^ 2) * (Real.log n) ^ 2 ∧
        ∀ s : ℕ, s.Prime → ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) → q ≤ s := by
  obtain ⟨r, hr, hbad⟩ := hbad
  have hlocal :=
    exists_prime_witness_le_nonKorselt_factor_log_sq hn ho (Nat.prime_of_mem_primeFactors hr)
      (Nat.dvd_of_mem_primeFactors hr) hbad hGRH
  exact exists_least_prime_witness_le_marked_factor_coefficient hn ho hc hr hlocal hGRH

end PseudoPrime.PrimeTestBounds.MillerRabin
