/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.PrimeCountPowerLower
public import PseudoPrime.Analysis.PrimeProductLogarithmicBudget
public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeProductCountingBounds

/-! # Unconditional log-power MR bounds from prime-power divisors -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Fix a>=2 and A>a/(a-1). For all sufficiently large odd primes p, every
odd n>1 divisible by p^a has a prime MR witness at most log(p)^A. Choose a natural
cutoff floor(log(p)^A) and k=ceil(c log(p)/log log(p)); unconditional Chebyshev
prime counts and two strict scale margins force a prime outside the local kernel. -/
theorem eventually_exists_prime_witness_le_log_prime_of_prime_pow {a : ℕ} (ha : 2 ≤ a) {A : ℝ}
    (hA : (a : ℝ) / ((a : ℝ) - 1) < A) :
    Filter.Eventually
      (fun p : ℕ ↦
        p.Prime →
          p ≠ 2 →
          ∀ n : ℕ,
            1 < n →
              Odd n →
              p ^ a ∣ n →
              ∃ r : ℕ,
                r.Prime ∧
                  (r : ℝ) ≤ (Real.log p) ^ A ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n))
      Filter.atTop := by
  have haR : (1 : ℝ) < a := by exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) ha)
  obtain ⟨b, c, hb, hbA, hc, hcA, hcb⟩ := Analysis.choose_log_count_parameters haR hA
  have hAp : 0 < A := (zero_lt_one.trans hb).trans hbA
  have hratio := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hgap := hratio.eventually_lt_const (div_pos (sub_pos.mpr hcA) hAp)
  have hL : Filter.Tendsto (fun p : ℕ ↦ Real.log p) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hM :=
    hL.eventually
      (NumberTheory.eventually_const_mul_rpow_le_primeCounting_floor_rpow (C := 2)
        (zero_lt_one.trans hb) hbA)
  have hfloor :=
    hL.eventually (NumberTheory.eventually_rpow_le_nat_floor_rpow (b := 0) (by norm_num only) hAp)
  have hlogc := hL.eventually (Real.tendsto_log_atTop.eventually_ge_atTop (2 * c))
  filter_upwards [hM, hfloor, hlogc, hL.eventually hgap, hL.eventually_ge_atTop 2] with p hMp hf hcL
    hg hLp hp hp2
  intro n hn ho hdiv
  let L := Real.log (p : ℝ)
  let B := Nat.floor (L ^ A)
  let k := Nat.ceil (c * L / Real.log L)
  have hL2 : 2 ≤ L := hLp
  have hL1 : 1 < L := lt_of_lt_of_le (by norm_num only) hL2
  have hLpos : 0 < L := zero_lt_one.trans hL1
  have hBpos : 0 < B := by
    apply (Nat.cast_pos (α := ℝ)).mp
    have hcast : (1 : ℝ) ≤ B := by simpa only [Real.rpow_zero] using hf
    exact zero_lt_one.trans_le hcast
  obtain ⟨hk, hkL, hklo, hkhi⟩ := Analysis.ceil_log_scale_bounds hc hL2 hcL
  have hgapL : c * A * L + A * Real.log L < (a : ℝ) * L := by
    have hm := (div_lt_div_iff₀ hLpos hAp).mp hg
    calc
      c * A * L + A * Real.log L < c * A * L + ((a : ℝ) - c * A) * L := by nlinarith only [hm]
      _ = (a : ℝ) * L := by ring
  have hsize : B ^ k < p ^ a :=
    Analysis.prime_power_product_lt_of_log_scale hp.pos hBpos hL1 hAp
      (Nat.floor_le (Real.rpow_nonneg hLpos.le A)) rfl hkhi hgapL
  have hbudget : (p - 1) * k ^ k < (B.primeCounting + 1 - k) ^ k :=
    Analysis.prime_product_power_budget_of_log_scale hp.pos hL1 hb hcb hk hkL hklo hMp le_rfl
  obtain ⟨r, hr, hrB, hrnot⟩ :=
    exists_prime_witness_of_prime_pow_power_budget hn ho hp hp2
      (lt_of_lt_of_le (by decide : 0 < 2) ha) hdiv B.primesLE k B
      (fun r hr ↦ (Nat.mem_primesLE.mp hr).2) (fun r hr ↦ (Nat.mem_primesLE.mp hr).1) hsize
      (by simpa only [Nat.primesLE_card_eq_primeCounting] using hbudget)
  exact ⟨r, hr, (Nat.cast_le.mpr hrB).trans (Nat.floor_le (Real.rpow_nonneg hLpos.le A)), hrnot⟩

/-- Fix a>=2 and A>a/(a-1). Eventually every odd n>1 having a prime a-th-power
divisor has a prime MR witness at most log(n)^A, without GRH. Large local primes
use the preceding log(p) bound; small ones are themselves bounded rejecting bases.
This gives a fixed exponent below two when a>=3 and A is chosen below two. -/
theorem eventually_exists_prime_witness_le_log_power_of_prime_pow_divisor {a : ℕ} (ha : 2 ≤ a)
    {A : ℝ} (hA : (a : ℝ) / ((a : ℝ) - 1) < A) :
    Filter.Eventually
      (fun n : ℕ ↦
        1 < n →
          Odd n →
          (∃ p : ℕ, p.Prime ∧ p ^ a ∣ n) →
          ∃ r : ℕ,
            r.Prime ∧ (r : ℝ) ≤ (Real.log n) ^ A ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n))
      Filter.atTop := by
  have haR : (1 : ℝ) < a := by exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) ha)
  have hAp : 0 < A := (div_pos (zero_lt_one.trans haR) (sub_pos.mpr haR)).trans hA
  obtain ⟨P, hP⟩ :=
    Filter.eventually_atTop.mp (eventually_exists_prime_witness_le_log_prime_of_prime_pow ha hA)
  have ht : Filter.Tendsto (fun n : ℕ ↦ (Real.log n) ^ A) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hAp).comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [ht.eventually_ge_atTop (P : ℝ)] with n hnb hn ho hdiv
  obtain ⟨p, hp, hpn⟩ := hdiv
  have hap : 0 < a := lt_of_lt_of_le (by decide : 0 < 2) ha
  have hpd : p ∣ n := (dvd_pow_self p hap.ne').trans hpn
  have hp2 : p ≠ 2 := fun he ↦ ho.not_two_dvd_nat (he ▸ hpd)
  by_cases hlarge : P ≤ p
  · obtain ⟨r, hr, hb, hf⟩ := hP p hlarge hp hp2 n hn ho hpn
    have hpLe : p ≤ n := Nat.le_of_dvd (Nat.zero_lt_of_lt hn) hpd
    have hl := Real.log_le_log (Nat.cast_pos.mpr hp.pos) (Nat.cast_le.mpr hpLe)
    have hl0 := Real.log_nonneg (Nat.one_le_cast.mpr hp.one_lt.le : (1 : ℝ) ≤ p)
    exact ⟨r, hr, hb.trans (Real.rpow_le_rpow hl0 hl hAp.le), hf⟩
  · exact
      ⟨p, hp, (Nat.cast_le.mpr (Nat.le_of_lt (Nat.lt_of_not_ge hlarge))).trans hnb,
        PrimeTest.strongMillerRabinPass_not_of_prime_dvd hn ho hp hpd⟩

/-- For fixed a>=2 and A>a/(a-1), the preceding unconditional eventual bound
also holds for the least prime MR rejecting base, including two. Minimize the
full prime-failure predicate for each input. No finite certificate or GRH is used. -/
theorem eventually_exists_least_prime_witness_le_log_power_of_prime_pow_divisor {a : ℕ} (ha : 2 ≤ a)
    {A : ℝ} (hA : (a : ℝ) / ((a : ℝ) - 1) < A) :
    Filter.Eventually
      (fun n : ℕ ↦
        1 < n →
          Odd n →
          (∃ p : ℕ, p.Prime ∧ p ^ a ∣ n) →
          ∃ r : ℕ,
            r.Prime ∧
              ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) ∧
              (r : ℝ) ≤ (Real.log n) ^ A ∧
              ∀ s : ℕ, s.Prime → ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) → r ≤ s)
      Filter.atTop := by
  classical
  apply (eventually_exists_prime_witness_le_log_power_of_prime_pow_divisor ha hA).mono
  intro n hn hng ho hdiv
  obtain ⟨r, hr, hb, hf⟩ := hn hng ho hdiv
  have hex : ∃ s : ℕ, s.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := ⟨r, hr, hf⟩
  exact
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2,
      (Nat.cast_le.mpr (Nat.find_min' hex ⟨hr, hf⟩)).trans hb, fun s hs hfail ↦
      Nat.find_min' hex ⟨hs, hfail⟩⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
