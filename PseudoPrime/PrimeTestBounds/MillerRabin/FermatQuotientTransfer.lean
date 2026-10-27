/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeProductCountingBounds
public import PseudoPrime.NumberTheory.PrimePowerNontrivial

/-! # Transferring nontrivial local Fermat powers to MR witnesses

External analytic estimates for Fermat quotients are explicit hypotheses.
This file proves their arithmetic transfer, not the estimates themselves.
-/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For an odd prime power p^a dividing n>1, a local unit killed by n-1
is killed by p-1. The ambient kernel has size gcd(p-1,n-1); apply Lagrange
inside that kernel and raise to a multiple. Used for Fermat-quotient transfer. -/
theorem local_fermat_kernel_le_prime_predecessor_kernel {n p a : ℕ} (hn : 1 < n) (hp : p.Prime)
    (hp2 : p ≠ 2) (ha : 0 < a) (hdiv : p ^ a ∣ n) (u : (ZMod (p ^ a))ˣ) (hu : u ^ (n - 1) = 1) :
    u ^ (p - 1) = 1 := by
  let : NeZero (p ^ a) := ⟨pow_ne_zero a hp.ne_zero⟩
  let H := (powMonoidHom (n - 1) : (ZMod (p ^ a))ˣ →* (ZMod (p ^ a))ˣ).ker
  let : Fintype H := Fintype.ofFinite H
  have hc : (⟨u, hu⟩ : H) ^ Nat.card H = 1 := by
    rw [Nat.card_eq_fintype_card]
    exact pow_card_eq_one
  have hv := congrArg (fun v : H ↦ (v : (ZMod (p ^ a))ˣ)) hc
  change u ^ Nat.card H = 1 at hv
  rw [card_local_fermat_kernel_prime_pow hn hp hp2 ha hdiv] at hv
  obtain ⟨t, ht⟩ := Nat.gcd_dvd_left (p - 1) (n - 1)
  rw [ht, pow_mul, hv, one_pow]

/-- If b^(p-1) is not one modulo an odd prime power p^a dividing odd n>1,
then b rejects n in MR. A pass would lie in the ambient Fermat kernel and
therefore in the (p-1)-power kernel. No GRH or primality of b is required. -/
theorem not_strongMillerRabinPass_of_local_prime_predecessor_power_ne_one {n p a b : ℕ} (hn : 1 < n)
    (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2) (ha : 0 < a) (hdiv : p ^ a ∣ n)
    (hbad : (b : ZMod (p ^ a)) ^ (p - 1) ≠ 1) :
    ¬PrimeTest.StrongMillerRabinPass n (b : ZMod n) := by
  let : NeZero (p ^ a) := ⟨pow_ne_zero a hp.ne_zero⟩
  intro hpass
  obtain ⟨u, hu, he⟩ :=
    PrimeTest.strongMillerRabinPass_mem_local_divisor_powerKernel hn ho hdiv hpass
  have hk :=
    local_fermat_kernel_le_prime_predecessor_kernel hn hp hp2 ha hdiv u (MonoidHom.mem_ker.mp hu)
  apply hbad
  calc
    (b : ZMod (p ^ a)) ^ (p - 1) = ↑(u ^ (p - 1)) := by rw [Units.val_pow_eq_pow_val, he]
    _ = 1 := by rw [hk, Units.val_one]

/-- A positive integer b with nontrivial (p-1)-power modulo p^a gives
an actual prime MR rejecting base at most b for every ambient odd n>1
divisible by p^a. Extract a prime factor, then use the local kernel transfer. -/
theorem exists_prime_witness_le_of_local_nontrivial_power {n p a b : ℕ} (hn : 1 < n) (ho : Odd n)
    (hp : p.Prime) (hp2 : p ≠ 2) (ha : 0 < a) (hdiv : p ^ a ∣ n) (hb : 0 < b)
    (hbad : (b : ZMod (p ^ a)) ^ (p - 1) ≠ 1) :
    ∃ r : ℕ, r.Prime ∧ r ≤ b ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  obtain ⟨r, hr, hle, hf⟩ := NumberTheory.exists_prime_le_of_nat_power_ne_one hb hbad
  exact
    ⟨r, hr, hle,
      not_strongMillerRabinPass_of_local_prime_predecessor_power_ne_one hn ho hp hp2 ha hdiv hf⟩

/-- An explicitly assumed positive integer with nontrivial local (p-1)-power
and real bound B gives an actual prime MR witness at most B.
The analytic bound remains an explicit hypothesis for future verified estimates. -/
theorem exists_prime_witness_le_of_fermat_quotient_bound {n p a : ℕ} (hn : 1 < n) (ho : Odd n)
    (hp : p.Prime) (hp2 : p ≠ 2) (ha : 0 < a) (hdiv : p ^ a ∣ n) (B : ℝ)
    (hbase : ∃ b : ℕ, 0 < b ∧ (b : ℝ) ≤ B ∧ (b : ZMod (p ^ a)) ^ (p - 1) ≠ 1) :
    ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ B ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  obtain ⟨b, hb, hle, hbad⟩ := hbase
  obtain ⟨r, hr, hsmall, hf⟩ :=
    exists_prime_witness_le_of_local_nontrivial_power hn ho hp hp2 ha hdiv hb hbad
  exact ⟨r, hr, (Nat.cast_le.mpr hsmall).trans hle, hf⟩

/-- For p^2 dividing odd n>1, assume a positive nontrivial local Fermat base
at most log(p)^alpha with alpha nonnegative. There is a prime MR witness
at most log(n)^alpha. Transfer the base and use p at most n and rpow monotonicity. -/
theorem exists_prime_witness_le_log_power_of_fermat_quotient_bound {n p : ℕ} (hn : 1 < n)
    (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2) (hdiv : p ^ 2 ∣ n) (alpha : ℝ) (halpha : 0 ≤ alpha)
    (hbase : ∃ b : ℕ, 0 < b ∧ (b : ℝ) ≤ (Real.log p) ^ alpha ∧ (b : ZMod (p ^ 2)) ^ (p - 1) ≠ 1) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (Real.log n) ^ alpha ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  obtain ⟨r, hr, hle, hf⟩ :=
    exists_prime_witness_le_of_fermat_quotient_bound hn ho hp hp2 (by norm_num only : 0 < (2 : ℕ))
      hdiv ((Real.log p) ^ alpha) hbase
  have hpn := Nat.le_of_dvd (Nat.zero_lt_of_lt hn) ((dvd_pow_self p (by decide)).trans hdiv)
  have hl := Real.log_le_log (Nat.cast_pos.mpr hp.pos) (Nat.cast_le.mpr hpn)
  have hl0 := Real.log_nonneg (Nat.one_le_cast.mpr hp.one_lt.le : (1 : ℝ) ≤ p)
  exact ⟨r, hr, hle.trans (Real.rpow_le_rpow hl0 hl halpha), hf⟩

/-- An explicitly assumed Fermat-quotient bound B also bounds the least prime
MR rejecting base. Minimize the full prime-failure predicate after the arithmetic
transfer. The external analytic estimate remains an explicit hypothesis. -/
theorem exists_least_prime_witness_le_of_fermat_quotient_bound {n p a : ℕ} (hn : 1 < n) (ho : Odd n)
    (hp : p.Prime) (hp2 : p ≠ 2) (ha : 0 < a) (hdiv : p ^ a ∣ n) (B : ℝ)
    (hbase : ∃ b : ℕ, 0 < b ∧ (b : ℝ) ≤ B ∧ (b : ZMod (p ^ a)) ^ (p - 1) ≠ 1) :
    ∃ r : ℕ,
      r.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) ∧
        (r : ℝ) ≤ B ∧
        ∀ s : ℕ, s.Prime → ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) → r ≤ s := by
  classical
  obtain ⟨r, hr, hb, hf⟩ :=
    exists_prime_witness_le_of_fermat_quotient_bound hn ho hp hp2 ha hdiv B hbase
  have hex : ∃ s : ℕ, s.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := ⟨r, hr, hf⟩
  exact
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2,
      (Nat.cast_le.mpr (Nat.find_min' hex ⟨hr, hf⟩)).trans hb, fun s hs hfail ↦
      Nat.find_min' hex ⟨hs, hfail⟩⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
