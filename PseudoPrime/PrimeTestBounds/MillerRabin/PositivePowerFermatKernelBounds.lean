/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.SmallFermatKernelAsymptoticBounds

/-! # Exact local Fermat kernel bounds for all positive prime-power exponents -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For a positive and 0<tau<a, division by a gives the subgroup exponent
beta=tau/a. The bound A>a/(a-tau) is exactly A>1/(1-beta).
Clear positive denominators using division cancellation. This includes a=1. -/
theorem positive_power_kernel_parameters {a : ℕ} (ha : 0 < a) {τ A : ℝ} (hτ : 0 < τ) (hτa : τ < a)
    (hA : (a : ℝ) / ((a : ℝ) - τ) < A) : 0 < τ / a ∧ τ / a < 1 ∧ 1 / (1 - τ / a) < A := by
  have ha0 : (0 : ℝ) < a := Nat.cast_pos.mpr ha
  have hd : 0 < (a : ℝ) - τ := sub_pos.mpr hτa
  have hb : τ / (a : ℝ) < 1 := (div_lt_one ha0).mpr hτa
  have he : (1 : ℝ) / (1 - τ / a) = (a : ℝ) / ((a : ℝ) - τ) := by
    apply (div_eq_div_iff (sub_pos.mpr hb).ne' hd.ne').mpr
    have hm := div_mul_cancel₀ τ ha0.ne'
    nlinarith only [hm]
  exact ⟨div_pos hτ ha0, hb, he ▸ hA⟩

/-- For a positive, 0<tau<a and A>a/(a-tau), all sufficiently large odd
primes p give prime MR witnesses for every odd n>1 divisible by p^a whose
exact ambient Fermat kernel has size at most p^tau. Apply the uniform subgroup
bound at modulus p^a, retaining exponent n-1. The threshold is independent of n. -/
theorem eventually_exists_prime_witness_of_positive_local_kernel {a : ℕ} (ha : 0 < a) {τ A : ℝ}
    (hτ : 0 < τ) (hτa : τ < a) (hA : (a : ℝ) / ((a : ℝ) - τ) < A) :
    ∀ᶠ p : ℕ in Filter.atTop,
      p.Prime →
        p ≠ 2 →
        ∀ n : ℕ,
          1 < n →
            Odd n →
            p ^ a ∣ n →
            (((p - 1).gcd (n - 1) : ℕ) : ℝ) ≤ (p : ℝ) ^ τ →
            ∃ r : ℕ,
              r.Prime ∧
                (r : ℝ) ≤ (Real.log ((p ^ a : ℕ) : ℝ)) ^ A ∧
                ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  obtain ⟨hb0, hb1, hbA⟩ := positive_power_kernel_parameters ha hτ hτa hA
  obtain ⟨Q, hQ⟩ :=
    Filter.eventually_atTop.mp
      (LLS.eventually_exists_prime_outside_le_log_power_of_card_rpow hb0 hb1 hbA)
  filter_upwards [Filter.eventually_ge_atTop Q] with p hpQ hp hp2
  intro n hn ho hdiv hcard
  have hpq : p ≤ p ^ a := Nat.le_of_dvd (pow_pos hp.pos a) (dvd_pow_self p ha.ne')
  let : NeZero (p ^ a) := ⟨pow_ne_zero a hp.ne_zero⟩
  let H := (powMonoidHom (n - 1) : (ZMod (p ^ a))ˣ →* (ZMod (p ^ a))ˣ).ker
  have hH : (Nat.card H : ℝ) ≤ ((p ^ a : ℕ) : ℝ) ^ (τ / a) := by
    rw [show Nat.card H = (p - 1).gcd (n - 1) from
        card_local_fermat_kernel_prime_pow hn hp hp2 ha hdiv]
    rw [Nat.cast_pow, ← Real.rpow_natCast_mul (Nat.cast_nonneg p)]
    have he : (a : ℝ) * (τ / a) = τ :=
      mul_div_cancel₀ τ (ne_of_gt (Nat.cast_pos.mpr ha : (0 : ℝ) < a))
    rw [he]
    exact hcard
  obtain ⟨r, hr, _, hb, hout⟩ := hQ (p ^ a) (hpQ.trans hpq) H hH
  refine ⟨r, hr, hb, ?_⟩
  intro hpass
  exact hout (PrimeTest.strongMillerRabinPass_mem_local_divisor_powerKernel hn ho hdiv hpass)

/-- For fixed positive a, 0<tau<a and A>a/(a-tau), sufficiently large odd n>1
with a prime-power divisor p^a and gcd(p-1,n-1)<=p^tau have a prime MR witness
at most log(n)^A. Large local primes use the uniform subgroup bound; bounded
local primes reject n themselves. Thus the threshold is uniform over p and n. -/
theorem eventually_exists_prime_witness_of_positive_power_kernel {a : ℕ} (ha : 0 < a) {τ A : ℝ}
    (hτ : 0 < τ) (hτa : τ < a) (hA : (a : ℝ) / ((a : ℝ) - τ) < A) :
    ∀ᶠ n : ℕ in Filter.atTop,
      1 < n →
        Odd n →
        (∃ p : ℕ, p.Prime ∧ p ^ a ∣ n ∧ (((p - 1).gcd (n - 1) : ℕ) : ℝ) ≤ (p : ℝ) ^ τ) →
        ∃ r : ℕ,
          r.Prime ∧
            (r : ℝ) ≤ (Real.log n) ^ A ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have haR : (0 : ℝ) < a := Nat.cast_pos.mpr ha
  have hAp : 0 < A := (div_pos haR (sub_pos.mpr hτa)).trans hA
  obtain ⟨P, hP⟩ :=
    Filter.eventually_atTop.mp
      (eventually_exists_prime_witness_of_positive_local_kernel ha hτ hτa hA)
  have ht : Filter.Tendsto (fun n : ℕ ↦ (Real.log n) ^ A) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hAp).comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [ht.eventually_ge_atTop (P : ℝ)] with n hnb hn ho hex
  obtain ⟨p, hp, hdiv, hcard⟩ := hex
  have hpd : p ∣ n := (dvd_pow_self p ha.ne').trans hdiv
  have hp2 : p ≠ 2 := fun he ↦ ho.not_two_dvd_nat (he ▸ hpd)
  by_cases hlarge : P ≤ p
  · obtain ⟨r, hr, hb, hf⟩ := hP p hlarge hp hp2 n hn ho hdiv hcard
    have hpLe : p ^ a ≤ n := Nat.le_of_dvd (Nat.zero_lt_of_lt hn) hdiv
    have hl := Real.log_le_log (Nat.cast_pos.mpr (pow_pos hp.pos a)) (Nat.cast_le.mpr hpLe)
    exact ⟨r, hr, hb.trans (Real.rpow_le_rpow (Real.log_natCast_nonneg _) hl hAp.le), hf⟩
  · exact
      ⟨p, hp, (Nat.cast_le.mpr (Nat.le_of_lt (Nat.lt_of_not_ge hlarge))).trans hnb,
        PrimeTest.strongMillerRabinPass_not_of_prime_dvd hn ho hp hpd⟩

/-- For fixed positive a, 0<tau<a and A>a/(a-tau), the least prime MR witness
obeys log(n)^A eventually on the exact-small-kernel family. Minimize the
constructed rejecting-prime predicate. This includes squarefree inputs when a=1. -/
theorem eventually_exists_least_prime_witness_of_positive_power_kernel {a : ℕ} (ha : 0 < a)
    {τ A : ℝ} (hτ : 0 < τ) (hτa : τ < a) (hA : (a : ℝ) / ((a : ℝ) - τ) < A) :
    ∀ᶠ n : ℕ in Filter.atTop,
      1 < n →
        Odd n →
        (∃ p : ℕ, p.Prime ∧ p ^ a ∣ n ∧ (((p - 1).gcd (n - 1) : ℕ) : ℝ) ≤ (p : ℝ) ^ τ) →
        ∃ r : ℕ,
          r.Prime ∧
            ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) ∧
            (r : ℝ) ≤ (Real.log n) ^ A ∧
            ∀ s : ℕ, s.Prime → ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) → r ≤ s := by
  classical
  apply (eventually_exists_prime_witness_of_positive_power_kernel ha hτ hτa hA).mono
  intro n hn hng ho hdiv
  obtain ⟨r, hr, hb, hf⟩ := hn hng ho hdiv
  have hex : ∃ s : ℕ, s.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := ⟨r, hr, hf⟩
  exact
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2,
      (Nat.cast_le.mpr (Nat.find_min' hex ⟨hr, hf⟩)).trans hb, fun s hs hfail ↦
      Nat.find_min' hex ⟨hs, hfail⟩⟩

/-- For fixed 0<tau<1 and A>1/(1-tau), every sufficiently large odd n>1
with a prime divisor p satisfying gcd(p-1,n-1)<=p^tau has least prime MR
witness at most log(n)^A. Specialize the positive-power theorem to a=1.
Squarefreeness is unrestricted, so this also covers the stated squarefree family. -/
theorem eventually_exists_least_prime_witness_of_prime_small_kernel {τ A : ℝ} (hτ0 : 0 < τ)
    (hτ1 : τ < 1) (hA : 1 / (1 - τ) < A) :
    ∀ᶠ n : ℕ in Filter.atTop,
      1 < n →
        Odd n →
        (∃ p : ℕ, p.Prime ∧ p ∣ n ∧ (((p - 1).gcd (n - 1) : ℕ) : ℝ) ≤ (p : ℝ) ^ τ) →
        ∃ r : ℕ,
          r.Prime ∧
            ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) ∧
            (r : ℝ) ≤ (Real.log n) ^ A ∧
            ∀ s : ℕ, s.Prime → ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) → r ≤ s := by
  simpa only [pow_one] using
    eventually_exists_least_prime_witness_of_positive_power_kernel (a := 1) (by norm_num only) hτ0
      (by simpa only [Nat.cast_one] using hτ1) (by simpa only [Nat.cast_one] using hA)

/-- If a is positive and 0<tau<a/2, choose a fixed exponent A<2 for the
exact-small-kernel family. The least prime MR witness is eventually bounded
by log(n)^A. This proves a subquadratic exponent for a=1 as well as higher powers. -/
theorem exists_subquadratic_exponent_of_positive_power_kernel {a : ℕ} (ha : 0 < a) {τ : ℝ}
    (hτ : 0 < τ) (hτhalf : τ < (a : ℝ) / 2) :
    ∃ A : ℝ,
      0 < A ∧
        A < 2 ∧
        ∀ᶠ n : ℕ in Filter.atTop,
          1 < n →
            Odd n →
            (∃ p : ℕ, p.Prime ∧ p ^ a ∣ n ∧ (((p - 1).gcd (n - 1) : ℕ) : ℝ) ≤ (p : ℝ) ^ τ) →
            ∃ r : ℕ,
              r.Prime ∧
                ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) ∧
                (r : ℝ) ≤ (Real.log n) ^ A ∧
                ∀ s : ℕ, s.Prime → ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) → r ≤ s := by
  have haR : (0 : ℝ) < a := Nat.cast_pos.mpr ha
  have hτa : τ < (a : ℝ) := by linarith only [haR, hτhalf]
  have hd : 0 < (a : ℝ) - τ := sub_pos.mpr hτa
  have hb : (a : ℝ) / ((a : ℝ) - τ) < 2 := by
    apply (div_lt_iff₀ hd).mpr
    linarith only [hτhalf]
  obtain ⟨A, hA, hA2⟩ := exists_between hb
  exact
    ⟨A, (div_pos haR hd).trans hA, hA2,
      eventually_exists_least_prime_witness_of_positive_power_kernel ha hτ hτa hA⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
