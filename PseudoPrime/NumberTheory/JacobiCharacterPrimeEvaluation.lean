/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.NumberTheory.JacobiCharacter
import PseudoPrime.NumberTheory.JacobiWitness.Smaller
import PseudoPrime.NumberTheory.JacobiWitness.Basic

/-!
# Evaluation of the quadratic character at odd primes

This file identifies the level-`4 * n` quadratic Dirichlet character with the Jacobi symbol
`J(n | ℓ)` at odd primes `ℓ` coprime to `n`.  The lifted `χ₄` factor supplies exactly the sign
required by quadratic reciprocity when both arguments are congruent to `3` modulo `4`.
-/

namespace PseudoPrime.NumberTheory

/--
For odd `n` and an odd prime `ℓ` coprime to `n`, the quadratic character attached to `n`
evaluates at `ℓ` as the Jacobi symbol `J(n | ℓ)`.  The proof first lifts coprimality from `n`
to `4 * n`, then separates the two odd residue classes modulo `4` for both arguments.
-/
theorem quadraticCharacter_apply_odd_prime (n : ℕ) (hn : Odd n) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓodd : Odd ℓ) (hcop : Nat.Coprime ℓ n) :
    quadraticCharacter n hn ((ℓ : ℤ) : ZMod (4 * n)) = jacobiSym n ℓ := by
  have hℓne2 : ℓ ≠ 2 := by
    intro hℓtwo
    subst ℓ
    obtain ⟨k, hk⟩ := hℓodd
    omega
  have hℓ4 : Nat.Coprime ℓ 4 := by
    have hℓ2 : Nat.Coprime ℓ 2 := (Nat.coprime_primes hℓ Nat.prime_two).mpr hℓne2
    have hpow := hℓ2.pow_right 2
    norm_num only at hpow
    exact hpow
  have hcop4n : Nat.Coprime ℓ (4 * n) := Nat.Coprime.mul_right hℓ4 hcop
  rw [quadraticCharacter_apply_of_coprime n hn hcop4n]
  rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hn) with hn1 | hn3
  · simp only [hn1, ite_true]
    exact (jacobiSym.quadratic_reciprocity_one_mod_four hn1 hℓodd).symm
  · rw [ite_eq_right (by omega : n % 4 ≠ 1)]
    rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hℓodd) with hℓ1 | hℓ3
    · have hchi : ZMod.χ₄ (((ℓ : ℤ) : ZMod 4)) = 1 := by
        simpa only [Int.cast_natCast] using ZMod.χ₄_nat_one_mod_four hℓ1
      rw [hchi, mul_one]
      exact jacobiSym.quadratic_reciprocity_one_mod_four hℓ1 hn
    · have hchi : ZMod.χ₄ (((ℓ : ℤ) : ZMod 4)) = -1 := by
        simpa only [Int.cast_natCast] using ZMod.χ₄_nat_three_mod_four hℓ3
      rw [hchi, jacobiSym.quadratic_reciprocity_three_mod_four hℓ3 hn3]
      ring

/-- Natural-cast form of `PseudoPrime.NumberTheory.quadraticCharacter_apply_odd_prime`. -/
theorem quadraticCharacter_apply_odd_prime_natCast (n : ℕ) (hn : Odd n) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓodd : Odd ℓ) (hcop : Nat.Coprime ℓ n) :
    quadraticCharacter n hn (ℓ : ZMod (4 * n)) = jacobiSym n ℓ := by
  simpa only [Int.cast_natCast] using quadraticCharacter_apply_odd_prime n hn hℓ hℓodd hcop

/--
The square of the integer-valued quadratic character attached to an odd modulus is the trivial
Dirichlet character.  On units this follows from the square laws for the Jacobi symbol and
`χ₄`; on nonunits both sides vanish.
-/
theorem quadraticCharacter_sq (n : ℕ) (hn : Odd n) : quadraticCharacter n hn ^ 2 = 1 := by
  let _ : NeZero (4 * n) := ⟨Nat.mul_ne_zero (by norm_num only) (Odd.pos hn).ne'⟩
  ext a
  rw [MulChar.pow_apply_coe, MulChar.one_apply_coe]
  have hcop4n : Nat.Coprime a.val.val (4 * n) := ZMod.val_coe_unit_coprime a
  have hcopn : Nat.Coprime a.val.val n := hcop4n.coprime_dvd_right (n.dvd_mul_left 4)
  have hgcd : (a.val.val : ℤ).gcd n = 1 := by simpa only [Int.gcd_natCast_natCast] using hcopn
  have hcop4 : Nat.Coprime a.val.val 4 := hcop4n.coprime_dvd_right (Nat.dvd_mul_right 4 n)
  have hunit4 : IsUnit (a.val.val : ZMod 4) := (ZMod.isUnit_iff_coprime _ _).mpr hcop4
  have hχunit : IsUnit (ZMod.χ₄ (a.val.val : ZMod 4)) := hunit4.map ZMod.χ₄
  have hχsq : ZMod.χ₄ (a.val.val : ZMod 4) ^ 2 = 1 := by
    rcases ZMod.isQuadratic_χ₄ (a.val.val : ZMod 4) with hzero | hone | hneg
    · exact (hχunit.ne_zero hzero).elim
    · rw [hone]
      norm_num only
    · rw [hneg]
      norm_num only
  rw [← ZMod.natCast_zmod_val a.val]
  have heval := quadraticCharacter_apply_of_coprime n hn hcop4n
  simp only [Int.cast_natCast] at heval
  rw [heval]
  split
  · exact jacobiSym.sq_one hgcd
  · rw [mul_pow, jacobiSym.sq_one hgcd]
    simpa only [one_mul] using hχsq

/-- The character attached to an odd modulus is quadratic. -/
theorem quadraticCharacter_isQuadratic (n : ℕ) (hn : Odd n) :
    (quadraticCharacter n hn).IsQuadratic :=
  MulChar.isQuadratic_iff_sq_eq_one.mpr (quadraticCharacter_sq n hn)

/-- At an odd prime coprime to `n`, the complex character is the cast of `J(n | ℓ)`. -/
theorem complexQuadraticCharacter_apply_odd_prime (n : ℕ) (hn : Odd n) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓodd : Odd ℓ) (hcop : Nat.Coprime ℓ n) :
    complexQuadraticCharacter n hn (ℓ : ZMod (4 * n)) = (jacobiSym n ℓ : ℂ) := by
  rw [complexQuadraticCharacter_apply,
    quadraticCharacter_apply_odd_prime_natCast n hn hℓ hℓodd hcop]

/-- The complex-valued quadratic character is quadratic. -/
theorem complexQuadraticCharacter_isQuadratic (n : ℕ) (hn : Odd n) :
    (complexQuadraticCharacter n hn).IsQuadratic :=
  (quadraticCharacter_isQuadratic n hn).comp (Int.castRingHom ℂ)

/-- The square of the complex-valued quadratic character is trivial. -/
theorem complexQuadraticCharacter_sq (n : ℕ) (hn : Odd n) :
    complexQuadraticCharacter n hn ^ 2 = 1 :=
  (complexQuadraticCharacter_isQuadratic n hn).sq_eq_one

/--
If an odd natural number `n` is not a square, its quadratic character is nontrivial.  For
`n > 3` a smaller odd-prime Jacobi `-1` witness detects nontriviality; the remaining modulus
`n = 3` is checked at the odd prime `5`.
-/
theorem quadraticCharacter_ne_one_of_not_square (n : ℕ) (hn : Odd n) (hns : ¬IsSquare n) :
    quadraticCharacter n hn ≠ 1 := by
  have hn1 : n ≠ 1 := by
    intro hnone
    subst n
    exact hns ((isSquare_iff_exists_sq 1).mpr ⟨1, by norm_num only⟩)
  have hn3 : n = 3 ∨ 3 < n := by
    have hnpos := Odd.pos hn
    obtain ⟨k, hk⟩ := hn
    omega
  refine MulChar.ne_one_iff.mpr ?_
  rcases hn3 with rfl | hn3
  · let u := ZMod.unitOfCoprime 5 (by norm_num only : Nat.Coprime 5 (4 * 3))
    refine ⟨u, ?_⟩
    rw [show (u : ZMod (4 * 3)) = (5 : ℕ) by exact ZMod.coe_unitOfCoprime _ _]
    have hvalue :=
      quadraticCharacter_apply_odd_prime_natCast 3 hn Nat.prime_five (by decide)
        (by norm_num only : Nat.Coprime 5 3)
    rw [hvalue]
    change jacobiSym (3 : ℤ) 5 ≠ 1
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    rw [← jacobiSym.legendreSym.to_jacobiSym 5 3]
    intro hone
    have hpow := legendreSym.eq_pow 5 3
    rw [hone] at hpow
    have hne : (1 : ZMod 5) ≠ 3 ^ ((5 - 1) / 2) := by
      intro hmod
      have hval := congrArg ZMod.val hmod
      change 1 = 4 at hval
      norm_num only at hval
    exact hne hpow
  · obtain ⟨q, hqprime, hqodd, _, hqvalue⟩ := oddNonsquareHasSmallerNegOneWitness hn hn3 hns
    let _ : NeZero q := ⟨hqprime.ne_zero⟩
    have hcop : Nat.Coprime q n := by
      rw [Nat.coprime_comm, Nat.coprime_iff_gcd_eq_one, ← Int.gcd_natCast_natCast]
      by_contra hgcd
      have hzero : jacobiSym n q = 0 := jacobi_eq_zero_iff_not_coprime.mpr hgcd
      omega
    have hqne2 : q ≠ 2 := by
      intro hqtwo
      subst q
      obtain ⟨k, hk⟩ := hqodd
      omega
    have hq4 : Nat.Coprime q 4 := by
      have hq2 := (Nat.coprime_primes hqprime Nat.prime_two).mpr hqne2
      have hpow := hq2.pow_right 2
      norm_num only at hpow
      exact hpow
    have hcop4n : Nat.Coprime q (4 * n) := Nat.Coprime.mul_right hq4 hcop
    let u := ZMod.unitOfCoprime q hcop4n
    refine ⟨u, ?_⟩
    rw [show (u : ZMod (4 * n)) = (q : ℕ) by exact ZMod.coe_unitOfCoprime _ _]
    have heq := quadraticCharacter_apply_odd_prime_natCast n hn hqprime hqodd hcop
    rw [hqvalue] at heq
    rw [heq]
    norm_num only

/-- For an odd nonsquare modulus, the complex-valued quadratic character is nontrivial. -/
theorem complexQuadraticCharacter_ne_one_of_not_square (n : ℕ) (hn : Odd n) (hns : ¬IsSquare n) :
    complexQuadraticCharacter n hn ≠ 1 := by
  rw [complexQuadraticCharacter]
  exact
    (MulChar.ringHomComp_ne_one_iff Int.cast_injective).mpr
      (quadraticCharacter_ne_one_of_not_square n hn hns)

/-- Convert a prime detected by the quadratic Dirichlet character at level `4 * n` into an
odd-prime Jacobi `-1` witness. Nondivisibility by `4*n` excludes `2` and the prime divisors of `n`;
quadratic reciprocity then turns the character value different from `1` into the required
Jacobi value. -/
theorem primeNegOneWitness_mem_of_complexQuadraticCharacter_ne_one (n : ℕ) (hn : Odd n) {ℓ : ℕ}
    (hℓprime : ℓ.Prime) (hℓndvd : ¬ℓ ∣ 4 * n) (hℓchar : complexQuadraticCharacter n hn ℓ ≠ 1) :
    ℓ ∈ PrimeNegOneWitnessSet n := by
  have hℓne2 : ℓ ≠ 2 := by
    intro hℓtwo
    subst ℓ
    exact hℓndvd (dvd_mul_of_dvd_left (by norm_num only : 2 ∣ 4) n)
  have hℓodd : Odd ℓ := hℓprime.odd_of_ne_two hℓne2
  have hℓndvdn : ¬ℓ ∣ n := by
    intro hℓdvdn
    exact hℓndvd (dvd_mul_of_dvd_right hℓdvdn 4)
  have hcop : Nat.Coprime ℓ n := hℓprime.coprime_iff_not_dvd.mpr hℓndvdn
  have hvalue := complexQuadraticCharacter_apply_odd_prime n hn hℓprime hℓodd hcop
  have hgcd : (n : ℤ).gcd ℓ = 1 := by exact_mod_cast hcop.symm.gcd_eq_one
  have hjacobi : jacobiSym n ℓ = -1 := by
    rcases jacobiSym.eq_one_or_neg_one hgcd with hone | hneg
    · exfalso
      apply hℓchar
      rw [hvalue, hone]
      norm_num only
    · exact hneg
  exact ⟨hℓprime, hℓodd, hjacobi⟩

end PseudoPrime.NumberTheory
