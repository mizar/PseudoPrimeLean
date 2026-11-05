/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.LocalFactorEnvelope
public import PseudoPrime.PrimeTestBounds.MillerRabin.FourNinthsSemiprimeBounds

/-! # Semiprime witnesses from local bounds and repeated-prime products -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For odd `n = p*q`, a prime supply of at least `M` through `B`, a product
size below `q`, and a multichoose count above `p` yield a rejecting prime at most
`B`. Convert the logarithmic conditions into the local kernel count; repeated
prime factors are allowed. The supply is independent of the chosen degree `k`. -/
theorem exists_prime_reject_semiprime_count {n p q B M k : ℕ} (hn : 1 < n) (ho : Odd n)
    (hp : p.Prime) (hq : q.Prime) (hprod : n = p * q) (hB : 1 < B) (hpi : M ≤ B.primeCounting)
    (hsize : (k : ℝ) * Real.log B < Real.log q)
    (hcount : Real.log p < Real.log (Nat.choose (M + k) k : ℝ)) :
    ∃ r : ℕ, r.Prime ∧ r ≤ B ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  obtain ⟨hpower, hgcd⟩ := semiprime_kernel_of_log_bounds hp hq hprod hB hsize hcount
  have hd : q ^ 1 ∣ n := by
    rw [pow_one, hprod]
    exact dvd_mul_left q p
  have hq2 : q ≠ 2 := ho.ne_two_of_dvd_nat (by simpa only [pow_one] using hd)
  exact
    exists_prime_multichoose_count_gcd hn ho hq hq2 (by norm_num only : 0 < 1) hd B M k hB hpi
      (by simpa only [pow_one] using hpower) hgcd

/-- Under GRH, for odd `n = p*q` with primes `p < q`, a supply of `M` primes
through `B`, and logarithmic bounds `k log B ≤ u` and `v ≤ log choose(M+k,k)`,
there is a rejecting prime at most `max B (V (max u (log n - v)))`. If the
larger factor's log is below the threshold, use the local envelope `V`; otherwise
both strict product-count inequalities follow. This is one general semiprime
candidate for every supply and degree. -/
theorem exists_prime_reject_semiprime_candidate {n p q B M k : ℕ} (hn : 1 < n) (ho : Odd n)
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q) (hprod : n = p * q) (hB : 1 < B)
    (hpi : M ≤ B.primeCounting) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {u v : ℝ} (hsize : (k : ℝ) * Real.log B ≤ u)
    (hcount : v ≤ Real.log (Nat.choose (M + k) k : ℝ)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ max (B : ℝ) (localFullEnvelope (max u (Real.log n - v))) ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hdiv : q ∣ n := by
    rw [hprod]
    exact dvd_mul_left q p
  have hbad : ¬q - 1 ∣ n - 1 := by
    rw [hprod]
    exact NumberTheory.not_sub_one_dvd_prime_mul_sub_one_of_lt hp hq hpq
  by_cases hlocal : Real.log q ≤ max u (Real.log n - v)
  · obtain ⟨r, hr, hb, hf⟩ := exists_prime_reject_nonKorselt_local hn ho hq hdiv hbad hGRH hlocal
    exact ⟨r, hr, hb.trans (le_max_right _ _), hf⟩
  · have hqbig : max u (Real.log n - v) < Real.log q := lt_of_not_ge hlocal
    have hsize' : (k : ℝ) * Real.log B < Real.log q :=
      hsize.trans_lt ((le_max_left _ _).trans_lt hqbig)
    have hlog : Real.log n = Real.log p + Real.log q := by
      rw [hprod, Nat.cast_mul,
        Real.log_mul (Nat.cast_ne_zero.mpr hp.ne_zero) (Nat.cast_ne_zero.mpr hq.ne_zero)]
    have hc : Real.log p < Real.log (Nat.choose (M + k) k : ℝ) := by
      have hh := (le_max_right u (Real.log n - v)).trans_lt hqbig
      linarith only [hlog, hh, hcount]
    obtain ⟨r, hr, hb, hf⟩ := exists_prime_reject_semiprime_count hn ho hp hq hprod hB hpi hsize' hc
    exact ⟨r, hr, (Nat.cast_le.mpr hb).trans (le_max_left _ _), hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
