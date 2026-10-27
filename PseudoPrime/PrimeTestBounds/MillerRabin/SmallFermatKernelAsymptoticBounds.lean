/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.SmallSubgroupPowerBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimePowerAsymptoticBounds

/-! # Unconditional MR log-power bounds retaining the exact local Fermat kernel -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For a≥2, 0<τ<a and A>a/(a-τ), set β=τ/a. Then 0<β<1 and
A>1/(1-β). Clear positive denominators. This supplies the existing small-subgroup
counting theorem with the exact local-kernel exponent. -/
theorem small_kernel_power_parameters {a : ℕ} (ha : 2 ≤ a) {τ A : ℝ} (hτ : 0 < τ) (hτa : τ < a)
    (hA : (a : ℝ) / ((a : ℝ) - τ) < A) : 0 < τ / a ∧ τ / a < 1 ∧ 1 / (1 - τ / a) < A := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) ha)
  have hd : 0 < (a : ℝ) - τ := sub_pos.mpr hτa
  have he : (1 : ℝ) / (1 - τ / a) = (a : ℝ) / ((a : ℝ) - τ) := by field_simp [ha0.ne', hd.ne']
  exact ⟨div_pos hτ ha0, (div_lt_one ha0).mpr hτa, he ▸ hA⟩

/-- Fix a≥2, 0<τ<a and A>a/(a-τ). For every sufficiently large odd prime p,
all odd n>1 divisible by p^a with gcd(p-1,n-1)≤p^τ have a prime MR rejecting
base through log(p^a)^A. Use the exact kernel cardinality and the uniform
small-subgroup theorem, then transfer local nonmembership to ambient MR failure.
The threshold is independent of n and no GRH is assumed. -/
theorem eventually_exists_prime_witness_le_local_log_of_small_fermat_kernel {a : ℕ} (ha : 2 ≤ a)
    {τ A : ℝ} (hτ : 0 < τ) (hτa : τ < a) (hA : (a : ℝ) / ((a : ℝ) - τ) < A) :
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
  obtain ⟨hb0, hb1, hbA⟩ := small_kernel_power_parameters ha hτ hτa hA
  obtain ⟨Q, hQ⟩ :=
    Filter.eventually_atTop.mp
      (LLS.eventually_exists_prime_outside_le_log_power_of_card_rpow hb0 hb1 hbA)
  filter_upwards [Filter.eventually_ge_atTop Q] with p hpQ hp hp2
  intro n hn ho hdiv hcard
  have ha0 : 0 < a := lt_of_lt_of_le (by decide : 0 < 2) ha
  have hpq : p ≤ p ^ a := Nat.le_of_dvd (pow_pos hp.pos a) (dvd_pow_self p ha0.ne')
  let : NeZero (p ^ a) := ⟨pow_ne_zero a hp.ne_zero⟩
  let H := (powMonoidHom (n - 1) : (ZMod (p ^ a))ˣ →* (ZMod (p ^ a))ˣ).ker
  have hH : (Nat.card H : ℝ) ≤ ((p ^ a : ℕ) : ℝ) ^ (τ / a) := by
    rw [show Nat.card H = (p - 1).gcd (n - 1) from
        card_local_fermat_kernel_prime_pow hn hp hp2 ha0 hdiv]
    rw [Nat.cast_pow, ← Real.rpow_natCast_mul (Nat.cast_nonneg p)]
    have he : (a : ℝ) * (τ / a) = τ := by field_simp [show (a : ℝ) ≠ 0 by exact_mod_cast ha0.ne']
    rw [he]
    exact hcard
  obtain ⟨r, hr, _, hb, hout⟩ := hQ (p ^ a) (hpQ.trans hpq) H hH
  refine ⟨r, hr, hb, ?_⟩
  intro hpass
  exact hout (PrimeTest.strongMillerRabinPass_mem_local_divisor_powerKernel hn ho hdiv hpass)

/-- Fix a≥2, 0<τ<a and A>a/(a-τ). Eventually every odd n>1 with a prime-power
divisor p^a and gcd(p-1,n-1)≤p^τ has a prime MR rejecting base through log(n)^A.
Large local primes use the uniform local bound and p^a≤n; bounded local primes
are themselves small rejecting bases. The start is uniform over n and p. -/
theorem eventually_exists_prime_witness_le_log_power_of_small_fermat_kernel {a : ℕ} (ha : 2 ≤ a)
    {τ A : ℝ} (hτ : 0 < τ) (hτa : τ < a) (hA : (a : ℝ) / ((a : ℝ) - τ) < A) :
    ∀ᶠ n : ℕ in Filter.atTop,
      1 < n →
        Odd n →
        (∃ p : ℕ, p.Prime ∧ p ^ a ∣ n ∧ (((p - 1).gcd (n - 1) : ℕ) : ℝ) ≤ (p : ℝ) ^ τ) →
        ∃ r : ℕ,
          r.Prime ∧
            (r : ℝ) ≤ (Real.log n) ^ A ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have haR : (0 : ℝ) < a := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) ha)
  have hAp : 0 < A := (div_pos haR (sub_pos.mpr hτa)).trans hA
  obtain ⟨P, hP⟩ :=
    Filter.eventually_atTop.mp
      (eventually_exists_prime_witness_le_local_log_of_small_fermat_kernel ha hτ hτa hA)
  have ht : Filter.Tendsto (fun n : ℕ ↦ (Real.log n) ^ A) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hAp).comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [ht.eventually_ge_atTop (P : ℝ)] with n hnb hn ho hex
  obtain ⟨p, hp, hdiv, hcard⟩ := hex
  have ha0 : 0 < a := lt_of_lt_of_le (by decide : 0 < 2) ha
  have hpd : p ∣ n := (dvd_pow_self p ha0.ne').trans hdiv
  have hp2 : p ≠ 2 := fun he ↦ ho.not_two_dvd_nat (he ▸ hpd)
  by_cases hlarge : P ≤ p
  · obtain ⟨r, hr, hb, hf⟩ := hP p hlarge hp hp2 n hn ho hdiv hcard
    have hpLe : p ^ a ≤ n := Nat.le_of_dvd (Nat.zero_lt_of_lt hn) hdiv
    have hl := Real.log_le_log (Nat.cast_pos.mpr (pow_pos hp.pos a)) (Nat.cast_le.mpr hpLe)
    exact ⟨r, hr, hb.trans (Real.rpow_le_rpow (Real.log_natCast_nonneg _) hl hAp.le), hf⟩
  · exact
      ⟨p, hp, (Nat.cast_le.mpr (Nat.le_of_lt (Nat.lt_of_not_ge hlarge))).trans hnb,
        PrimeTest.strongMillerRabinPass_not_of_prime_dvd hn ho hp hpd⟩

/-- Under the fixed parameter bounds, every sufficiently large odd input with
the stated prime-power divisor and small exact local kernel has a least prime
MR rejecting base at most log(n)^A. Minimize the complete prime-failure predicate.
This connects the unconditional family bound to the actual least MR witness. -/
theorem eventually_exists_least_prime_witness_le_log_power_of_small_fermat_kernel {a : ℕ}
    (ha : 2 ≤ a) {τ A : ℝ} (hτ : 0 < τ) (hτa : τ < a) (hA : (a : ℝ) / ((a : ℝ) - τ) < A) :
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
  apply (eventually_exists_prime_witness_le_log_power_of_small_fermat_kernel ha hτ hτa hA).mono
  intro n hn hng ho hdiv
  obtain ⟨r, hr, hb, hf⟩ := hn hng ho hdiv
  have hex : ∃ s : ℕ, s.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := ⟨r, hr, hf⟩
  exact
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2,
      (Nat.cast_le.mpr (Nat.find_min' hex ⟨hr, hf⟩)).trans hb, fun s hs hfail ↦
      Nat.find_min' hex ⟨hs, hfail⟩⟩

/-- Fix 0<σ<1 and A>2/(1+σ). For sufficiently large odd n>1 with p² dividing n
and gcd(p-1,n-1)≤p^(1-σ), the least prime MR rejecting base is at most log(n)^A.
Specialize the uniform prime-power theorem to a=2 and τ=1-σ.
This permits exponents below two for a family of square-divisible inputs. -/
theorem eventually_exists_least_prime_witness_le_log_power_of_square_small_kernel {σ A : ℝ}
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (hA : 2 / (1 + σ) < A) :
    ∀ᶠ n : ℕ in Filter.atTop,
      1 < n →
        Odd n →
        (∃ p : ℕ, p.Prime ∧ p ^ 2 ∣ n ∧ (((p - 1).gcd (n - 1) : ℕ) : ℝ) ≤ (p : ℝ) ^ (1 - σ)) →
        ∃ r : ℕ,
          r.Prime ∧
            ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) ∧
            (r : ℝ) ≤ (Real.log n) ^ A ∧
            ∀ s : ℕ, s.Prime → ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) → r ≤ s := by
  apply
    eventually_exists_least_prime_witness_le_log_power_of_small_fermat_kernel (a := 2) (τ := 1 - σ)
      (by decide)
  · linarith only [hσ1]
  · norm_num only [Nat.cast_ofNat]
    linarith only [hσ0]
  · norm_num only [Nat.cast_ofNat]
    rw [show (2 : ℝ) - (1 - σ) = 1 + σ by ring]
    exact hA

/-- For fixed 0<σ<1, some positive A<2 bounds the least prime MR witness by
log(n)^A eventually on the stated square-divisible small-kernel family.
Choose A strictly between 2/(1+σ) and 2 and apply the uniform square theorem.
No GRH, external Fermat-quotient theorem or finite certificate is used. -/
theorem exists_subquadratic_exponent_for_square_small_fermat_kernel {σ : ℝ} (hσ0 : 0 < σ)
    (hσ1 : σ < 1) :
    ∃ A : ℝ,
      0 < A ∧
        A < 2 ∧
        ∀ᶠ n : ℕ in Filter.atTop,
          1 < n →
            Odd n →
            (∃ p : ℕ, p.Prime ∧ p ^ 2 ∣ n ∧ (((p - 1).gcd (n - 1) : ℕ) : ℝ) ≤ (p : ℝ) ^ (1 - σ)) →
            ∃ r : ℕ,
              r.Prime ∧
                ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) ∧
                (r : ℝ) ≤ (Real.log n) ^ A ∧
                ∀ s : ℕ, s.Prime → ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) → r ≤ s := by
  have hd : 0 < 1 + σ := by linarith only [hσ0]
  have hb : (2 : ℝ) / (1 + σ) < 2 := by
    apply (div_lt_iff₀ hd).mpr
    linarith only [hσ0]
  obtain ⟨A, hA, hA2⟩ := exists_between hb
  exact
    ⟨A, (div_pos (by norm_num only : (0 : ℝ) < 2) hd).trans hA, hA2,
      eventually_exists_least_prime_witness_le_log_power_of_square_small_kernel hσ0 hσ1 hA⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
