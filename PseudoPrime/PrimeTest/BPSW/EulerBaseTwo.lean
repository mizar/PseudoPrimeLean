/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.BPSW.EulerModEight
public import PseudoPrime.PrimeTest.MillerRabin.WitnessSubgroup

/-! # Base-two Strong MR implies Euler-Jacobi for every odd modulus greater than one

For the one-modulo-eight branch, a hypothetical last minus-one stage forces each prime
factor to be one modulo a larger two-power. Square roots of two strengthen the local
index bound, and the prime-factor product contradicts the valuation of n-1.
Combine all congruence branches and connect signed powers to the execution and paper contracts.
-/

@[expose] public section

namespace PseudoPrime.PrimeTest.EulerRedundancy

/-- Two is nonzero modulo any prime other than two.
A zero residue would make that prime divide two; used for Fermat and square-root arguments. -/
theorem two_nonzero {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro hz
  have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa only [Nat.cast_ofNat] using hz)
  exact hp2 ((Nat.prime_two.eq_one_or_self_of_dvd p hd).resolve_left hp.ne_one)

/-- A minus-one power of two has index below the two-adic valuation of p-1.
For an odd prime p, Fermat and the existing negative-power index bound give
the strict inequality. -/
theorem local_index_bound {p j d : ℕ} (hp : p.Prime) (ho : Odd p)
    (hn : (2 : ZMod p) ^ (2 ^ j * d) = -1) : j < padicValNat 2 (p - 1) := by
  let : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := fun h ↦ (Nat.not_even_iff_odd.mpr ho) (h ▸ (by decide : Even 2))
  have hf := ZMod.pow_card_sub_one_eq_one (two_nonzero hp hp2)
  exact Nat.lt_of_not_ge (fun ht ↦ neg_power_index_lt_twoAdicExponent hp ho ht hf hn)

/-- An odd prime with eight dividing p-1 is one modulo eight.
Natural modular congruence transfers the subtraction divisibility to the required remainder. -/
theorem mod_eight_one_of_dvd_sub {p : ℕ} (hp : p.Prime) (hd : 8 ∣ p - 1) : p % 8 = 1 := by
  have hm : Nat.ModEq 8 1 p := (Nat.modEq_iff_dvd' hp.one_lt.le).mpr hd
  exact hm.symm

/-- For a prime one modulo eight, two has a nonzero square root modulo that prime.
The supplementary quadratic-residue criterion supplies the root; two being nonzero excludes zero. -/
theorem sqrt_two_nonzero {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hm : p % 8 = 1) :
    ∃ y : ZMod p, (2 : ZMod p) = y ^ 2 ∧ y ≠ 0 := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨y, hy⟩ :=
    (isSquare_iff_exists_sq (2 : ZMod p)).mp ((ZMod.exists_sq_eq_two_iff hp2).mpr (Or.inl hm))
  have hy0 : y ≠ 0 := by
    intro hz
    rw [hz, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hy
    exact two_nonzero hp hp2 hy
  exact ⟨y, hy, hy0⟩

/-- For positive s, the canonical power exponent doubles its predecessor exponent.
This arithmetic identity lifts a minus-one stage through a square root. -/
theorem double_power_exponent {s d : ℕ} (hs : 0 < s) : 2 ^ s * d = 2 * (2 ^ (s - 1) * d) := by
  rw [← Nat.mul_assoc, ← Nat.pow_succ', Nat.succ_eq_add_one, Nat.sub_add_cancel hs]

/-- A square root of two has a minus-one stage one index above that of two.
For positive s, substitute the square into the doubled exponent identity. -/
theorem sqrt_minus_stage {p s d : ℕ} (hs : 0 < s) {y : ZMod p} (hy : (2 : ZMod p) = y ^ 2)
    (hn : (2 : ZMod p) ^ (2 ^ (s - 1) * d) = -1) : y ^ (2 ^ s * d) = -1 := by
  rw [double_power_exponent hs, pow_mul, ← hy]
  exact hn

/-- A high minus-one stage of two forces an extra two-adic factor in p-1.
For an odd prime and s at least three, the first index bound makes p one modulo eight.
A square root of two then lifts the stage and gives the stronger index bound. -/
theorem local_index_strict {p s d : ℕ} (hp : p.Prime) (ho : Odd p) (hs : 3 ≤ s)
    (hn : (2 : ZMod p) ^ (2 ^ (s - 1) * d) = -1) : s < padicValNat 2 (p - 1) := by
  let : Fact p.Prime := ⟨hp⟩
  have hspos : 0 < s := lt_of_lt_of_le (by decide : 0 < 3) hs
  have hst : s ≤ padicValNat 2 (p - 1) := by
    simpa only [Nat.succ_eq_add_one, Nat.sub_add_cancel hspos] using
      Nat.succ_le_of_lt (local_index_bound hp ho hn)
  have h8 : 8 ∣ p - 1 := (padicValNat_dvd_iff 3 (p - 1)).mpr (Or.inr (hs.trans hst))
  have hp2 : p ≠ 2 := fun h ↦ (Nat.not_even_iff_odd.mpr ho) (h ▸ (by decide : Even 2))
  obtain ⟨y, hy, hy0⟩ := sqrt_two_nonzero hp hp2 (mod_eight_one_of_dvd_sub hp h8)
  exact
    Nat.lt_of_not_ge
      (fun hu ↦
        neg_power_index_lt_twoAdicExponent hp ho hu (ZMod.pow_card_sub_one_eq_one hy0)
          (sqrt_minus_stage hspos hy hn))

/-- A prime divisor of an odd number is odd.
Divisibility by two would contradict the modulus parity; used by each prime-local bound. -/
theorem prime_divisor_odd {n p : ℕ} (ho : Odd n) (hp : p.Prime) (hd : p ∣ n) : Odd p := by
  have hp2 : p ≠ 2 := fun h ↦ (Nat.not_even_iff_odd.mpr ho) (even_iff_two_dvd.mpr (h ▸ hd))
  exact hp.odd_of_ne_two hp2

/-- A minus-one power of two descends to every divisor modulus.
The canonical ring homomorphism preserves powers, numeral two, and the sign. -/
theorem minus_cast {n p e : ℕ} (hd : p ∣ n) (h : (2 : ZMod n) ^ e = -1) :
    (2 : ZMod p) ^ e = -1 := by
  have ht := congrArg (ZMod.castHom hd (ZMod p)) h
  simpa only [map_pow, map_ofNat, map_neg, map_one] using ht

/-- Each prime divisor of a high last-stage minus-one modulus is one modulo the next two-power.
For odd n and s at least three, descend the stage and apply the strict prime-local index bound. -/
theorem prime_dvd_next_power {n p s d : ℕ} (ho : Odd n) (hs : 3 ≤ s)
    (hn : (2 : ZMod n) ^ (2 ^ (s - 1) * d) = -1) (hp : p.Prime) (hd : p ∣ n) :
    2 ^ (s + 1) ∣ p - 1 := by
  have ht := local_index_strict hp (prime_divisor_odd ho hp hd) hs (minus_cast hd hn)
  exact (padicValNat_dvd_iff_le (Nat.sub_ne_zero_of_lt hp.one_lt)).mpr (Nat.succ_le_of_lt ht)

/-- A list of residues all congruent to one has product congruent to one.
The list may contain repeated factors; multiplication of congruences proves the contract. -/
theorem prod_mod_one (m : ℕ) (xs : List ℕ) (h : ∀ p ∈ xs, Nat.ModEq m 1 p) :
    Nat.ModEq m 1 xs.prod := by
  revert h
  induction xs with
  | nil =>
    intro _
    exact Nat.ModEq.refl 1
  | cons a xs ih =>
    intro h
    have ha := h a (List.mem_cons_self)
    have ht := ih (fun p hp ↦ h p (List.mem_cons_of_mem a hp))
    simpa only [List.prod_cons, one_mul] using ha.mul ht

/-- A high last-stage minus-one modulus is itself one modulo the next two-power.
Every prime factor, including multiplicities, satisfies the congruence,
so their product does too. -/
theorem factors_mod_one {n s d : ℕ} (hn : 1 < n) (ho : Odd n) (hs : 3 ≤ s)
    (hneg : (2 : ZMod n) ^ (2 ^ (s - 1) * d) = -1) : Nat.ModEq (2 ^ (s + 1)) 1 n := by
  rw [← Nat.prod_primeFactorsList (Nat.ne_zero_of_lt hn)]
  apply prod_mod_one
  intro p hp
  exact
    (Nat.modEq_iff_dvd' (Nat.prime_of_mem_primeFactorsList hp).one_lt.le).mpr
      (prime_dvd_next_power ho hs hneg (Nat.prime_of_mem_primeFactorsList hp)
        (Nat.dvd_of_mem_primeFactorsList hp))

/-- The last minus-one stage is impossible when the canonical valuation is at least three.
For odd n greater than one, the prime-factor product would raise the valuation of n-1.
This contradiction closes the remaining one-modulo-eight Euler branch. -/
theorem last_stage_impossible {n s d : ℕ} (hn : 1 < n) (ho : Odd n) (hs : 3 ≤ s)
    (hval : padicValNat 2 (n - 1) = s) : (2 : ZMod n) ^ (2 ^ (s - 1) * d) ≠ -1 := by
  intro hneg
  have hd := (Nat.modEq_iff_dvd' hn.le).mp (factors_mod_one hn ho hs hneg)
  have hv := (padicValNat_dvd_iff_le (Nat.sub_ne_zero_of_lt hn)).mp hd
  rw [hval] at hv
  exact Nat.not_succ_le_self s hv

/-- For odd n greater than one, n/2 is the canonical predecessor two-power times the odd part.
The factorization of n-1 and the twice-half identity identify this exponent. -/
theorem canonical_half_index {n : ℕ} (hn : 1 < n) (ho : Odd n) :
    n / 2 = 2 ^ (padicValNat 2 (n - 1) - 1) * Nat.divMaxPow (n - 1) 2 := by
  obtain ⟨hs, _, hd⟩ := odd_sub_canonical_decomp hn ho
  have he := double_power_exponent (d := Nat.divMaxPow (n - 1) 2) hs
  rw [he] at hd
  have ht := odd_twice_half hn ho
  nlinarith only [hd, ht]

/-- Every accepted minus-one stage lies strictly before the last when the valuation is high.
The MR index bound and impossibility of the last stage give the inequality. -/
theorem minus_index_lt_last {n j : ℕ} (hn : 1 < n) (ho : Odd n) (hs : 3 ≤ padicValNat 2 (n - 1))
    (hj : j < padicValNat 2 (n - 1)) (hp : (2 : ZMod n) ^ (2 ^ j * Nat.divMaxPow (n - 1) 2) = -1) :
    j < padicValNat 2 (n - 1) - 1 := by
  have hjne : j ≠ padicValNat 2 (n - 1) - 1 := fun he ↦ last_stage_impossible hn ho hs rfl (he ▸ hp)
  have hjle : j ≤ padicValNat 2 (n - 1) - 1 := by
    simpa only [Nat.pred_eq_sub_one] using Nat.le_pred_of_lt hj
  exact lt_of_le_of_ne hjle hjne

/-- A minus-one stage strictly before the half-index stage extends to half-index power one.
The remaining two-power is even, so its power of minus one is one. -/
theorem earlier_minus_half_pow {n j : ℕ} (hn : 1 < n) (ho : Odd n)
    (hj : j < padicValNat 2 (n - 1) - 1)
    (hp : (2 : ZMod n) ^ (2 ^ j * Nat.divMaxPow (n - 1) 2) = -1) : (2 : ZMod n) ^ (n / 2) = 1 := by
  have he :
    (2 ^ j * Nat.divMaxPow (n - 1) 2) * 2 ^ (padicValNat 2 (n - 1) - 1 - j) =
      2 ^ (padicValNat 2 (n - 1) - 1) * Nat.divMaxPow (n - 1) 2 := by
    rw [Nat.mul_right_comm, ← Nat.pow_add, Nat.add_sub_of_le hj.le]
  have heven : Even (2 ^ (padicValNat 2 (n - 1) - 1 - j)) :=
    (show Even 2 from ⟨1, rfl⟩).pow_of_ne_zero (Nat.ne_of_gt (Nat.sub_pos_of_lt hj))
  rw [canonical_half_index hn ho, ← he, pow_mul, hp]
  exact heven.neg_one_pow

/-- A base-two Strong MR pass has half-index power one when the valuation of n-1 is at least three.
For odd n greater than one, exclude the last minus-one stage and extend the remaining branches. -/
theorem half_pow_one_large {n : ℕ} (hn : 1 < n) (ho : Odd n) (hs : 3 ≤ padicValNat 2 (n - 1))
    (h : IsStrongMillerRabinProbablePrime n 2) : (2 : ZMod n) ^ (n / 2) = 1 := by
  have hp : StrongMillerRabinPass n (2 : ZMod n) := by
    simpa only [Nat.cast_ofNat] using isStrongMillerRabinProbablePrime_iff_pass.mp h
  rcases hp with hp | ⟨j, hj, hp⟩
  · rw [canonical_half_index hn ho, Nat.mul_comm, pow_mul, hp, one_pow]
  · exact earlier_minus_half_pow hn ho (minus_index_lt_last hn ho hs hj hp) hp

/-- A modulus one modulo eight and greater than one is odd with valuation of n-1 at least three.
Reduction modulo four and divisibility by eight supply the hypotheses of the half-power theorem. -/
theorem one_mod_eight_data {n : ℕ} (hn : 1 < n) (hm : n % 8 = 1) :
    Odd n ∧ 3 ≤ padicValNat 2 (n - 1) := by
  have h4 : n % 4 = 1 := by rw [← Nat.mod_mod_of_dvd n (by norm_num only : 4 ∣ 8), hm]
  have h8 : 8 ∣ n - 1 := (Nat.modEq_iff_dvd' hn.le).mp hm.symm
  exact
    ⟨Nat.odd_iff.mpr (Nat.odd_mod_four_iff.mpr (Or.inl h4)),
      (padicValNat_dvd_iff_le (Nat.sub_ne_zero_of_lt hn)).mp h8⟩

/-- The Jacobi symbol of two is one for a modulus one modulo eight greater than one.
Evaluate the supplementary character without assuming primality. -/
theorem jacobi_two_one {n : ℕ} (hn : 1 < n) (hm : n % 8 = 1) : jacobiSym 2 n = 1 := by
  have ho := (one_mod_eight_data hn hm).1
  rw [jacobiSym.at_two ho, ZMod.χ₈_nat_eq_if_mod_eight]
  norm_num only [hm, Nat.odd_iff.mp ho, ite_false, true_or, ite_true]

/-- Base-two Strong MR implies Euler-Jacobi for a modulus one modulo eight greater than one.
The half-index power and Jacobi symbol are both one;
this completes the missing congruence branch. -/
theorem euler_of_strong_one {n : ℕ} (hn : 1 < n) (hm : n % 8 = 1)
    (h : IsStrongMillerRabinProbablePrime n 2) : IsEulerJacobiProbablePrimeInt n 2 := by
  simp only [IsEulerJacobiProbablePrimeInt, Int.cast_ofNat, jacobi_two_one hn hm, Int.cast_one]
  exact half_pow_one_large hn (one_mod_eight_data hn hm).1 (one_mod_eight_data hn hm).2 h

/-- A number one modulo four is either one or five modulo eight.
The quotient of its remainder by four is zero or one; used to combine the two Euler branches. -/
theorem mod_eight_one_or_five {n : ℕ} (hm : n % 4 = 1) : n % 8 = 1 ∨ n % 8 = 5 := by
  have hd := Nat.div_add_mod (n % 8) 4
  have h4 : (n % 8) % 4 = 1 := by rw [Nat.mod_mod_of_dvd n (by norm_num only : 4 ∣ 8), hm]
  rw [h4] at hd
  have hq : (n % 8) / 4 < 2 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 4)).mpr
      (by simpa only [Nat.reduceMul] using Nat.mod_lt n (by decide : 0 < 8))
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.le_of_lt_succ hq) with hq | hq
  · rw [hq] at hd
    exact Or.inl hd.symm
  · rw [hq] at hd
    exact Or.inr hd.symm

/-- For every odd n greater than one, base-two Strong MR implies Euler-Jacobi.
Combine the three-modulo-four, five-modulo-eight, and one-modulo-eight proofs.
This removes the remaining arithmetic hypothesis from signed-power Euler omission. -/
theorem euler_of_strong_two {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (h : IsStrongMillerRabinProbablePrime n 2) : IsEulerJacobiProbablePrimeInt n 2 := by
  rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp ho) with hm | hm
  · rcases mod_eight_one_or_five hm with h8 | h8
    · exact euler_of_strong_one hn h8 h
    · exact euler_of_strong_five h8 h
  · exact euler_of_strong 2 hm h

/-- Every signed power of two satisfies Euler after base-two Strong MR for odd n greater than one.
Power and negation closure include exponent zero and both signs.
The theorem justifies the full signed-power eligibility guard. -/
theorem euler_signed_two_power_all {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (h : IsStrongMillerRabinProbablePrime n 2) {Q : ℤ} (k : ℕ)
    (hQ : Q = (2 : ℤ) ^ k ∨ Q = -(2 : ℤ) ^ k) : IsEulerJacobiProbablePrimeInt n Q := by
  have he := euler_pow (euler_of_strong_two hn ho h) k
  rcases hQ with hQ | hQ
  · exact hQ ▸ he
  · exact hQ ▸ euler_neg ho he

/-- The shared strengthened evaluator reduces to Strong and V for any signed power of two.
For odd n greater than one with base-two MR passed, the Euler flag is true.
This equality is consumed by the conditional execution entry. -/
theorem strengthened_without_euler_all {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (h : IsStrongMillerRabinProbablePrime n 2) (param : LucasParams) (k : ℕ)
    (hQ : param.Q = (2 : ℤ) ^ k ∨ param.Q = -(2 : ℤ) ^ k) :
    strengthenedLucasSharedEulerValid n param =
      (strongLucasWithParams n param.D param.P param.Q &&
        lucasVWithParams n param.D param.P param.Q) := by
  have he := eulerJacobiWithIntBase_eq_true_iff.mpr (euler_signed_two_power_all hn ho h k hQ)
  rw [strengthenedLucasSharedEulerValid_eq, strengthenedLucasSharedEuler_eq, he, Bool.and_true]

/-- The paper conditions reduce to Strong and terminal V for every signed power of two.
For odd n greater than one with MR passed, multiplied Euler follows without cancellation.
This supplies the independent specification consumer of the full arithmetic theorem. -/
theorem bfw_without_euler_all {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (h : IsStrongMillerRabinProbablePrime n 2) (param : LucasParams) (k : ℕ)
    (hQ : param.Q = (2 : ℤ) ^ k ∨ param.Q = -(2 : ℤ) ^ k) :
    BFWLucasConditions n param ↔
      IsStrongLucasProbablePrime n param ∧
        lucasVZMod n param.P param.Q (n + 1) = 2 * (param.Q : ZMod n) := by
  have he := multiplied_euler ho (euler_signed_two_power_all hn ho h k hQ)
  simp only [BFWLucasConditions, he, and_true]

end PseudoPrime.PrimeTest.EulerRedundancy
