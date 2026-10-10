/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.BPSW.EulerRedundancy

/-! # Euler redundancy for the five-modulo-eight MR branch

Evaluate the Jacobi characters to exclude the initial-one and zero-index minus-one
branches. The remaining MR stage fixes the half-index sign, including composite moduli.
Connect signed powers of two to the shared evaluator and the independent paper conditions.
-/

@[expose] public section

namespace PseudoPrime.PrimeTest.EulerRedundancy

/-- A remainder of five modulo eight implies a remainder of one modulo four.
Reduce the known remainder through divisibility; used by the minus-one Jacobi character. -/
theorem mod_eight_five_four {n : ℕ} (hm : n % 8 = 5) : n % 4 = 1 := by
  rw [← Nat.mod_mod_of_dvd n (by norm_num only : 4 ∣ 8), hm]

/-- A modulus five modulo eight is greater than one, odd, and one modulo four.
The remainder bound and parity law supply the canonical MR and Jacobi hypotheses. -/
theorem mod_eight_five_data {n : ℕ} (hm : n % 8 = 5) : 1 < n ∧ Odd n ∧ n % 4 = 1 := by
  have hn : 5 ≤ n := hm ▸ Nat.mod_le n 8
  have h4 := mod_eight_five_four hm
  exact
    ⟨Nat.lt_of_lt_of_le (by norm_num only : 1 < 5) hn,
      Nat.odd_iff.mpr (Nat.odd_mod_four_iff.mpr (Or.inl h4)), h4⟩

/-- Subtracting one from a modulus five modulo eight leaves remainder four.
The quotient equation and n greater than one justify subtraction in natural numbers. -/
theorem sub_mod_eight_five {n : ℕ} (hm : n % 8 = 5) : (n - 1) % 8 = 4 := by
  have hd := Nat.div_add_mod n 8
  rw [hm] at hd
  have hs := Nat.sub_add_cancel (Nat.le_of_lt (mod_eight_five_data hm).1)
  have he : n - 1 = 8 * (n / 8) + 4 := by nlinarith only [hd, hs]
  rw [he, Nat.add_mod, Nat.mul_mod]
  norm_num only [Nat.zero_mul, Nat.zero_add]

/-- Four divides n-1 for a modulus five modulo eight.
Reducing the remainder modulo four gives the lower bound on the two-adic valuation. -/
theorem four_dvd_sub_five {n : ℕ} (hm : n % 8 = 5) : 4 ∣ n - 1 := by
  apply Nat.dvd_of_mod_eq_zero
  rw [← Nat.mod_mod_of_dvd (n - 1) (by norm_num only : 4 ∣ 8), sub_mod_eight_five hm]

/-- Eight does not divide n-1 for a modulus five modulo eight.
Its remainder is four, which excludes any higher canonical two-adic exponent. -/
theorem eight_not_dvd_sub_five {n : ℕ} (hm : n % 8 = 5) : ¬8 ∣ n - 1 := by
  intro hd
  have hz := Nat.mod_eq_zero_of_dvd hd
  rw [sub_mod_eight_five hm] at hz
  norm_num only at hz

/-- The two-adic valuation of n-1 is exactly two when n is five modulo eight.
Divisibility by four and nondivisibility by eight determine the valuation.
This bounds the accepted minus-one stage to zero or one. -/
theorem twoAdic_eq_two {n : ℕ} (hm : n % 8 = 5) : padicValNat 2 (n - 1) = 2 := by
  have hn := Nat.sub_ne_zero_of_lt (mod_eight_five_data hm).1
  have hlo : 2 ≤ padicValNat 2 (n - 1) := (padicValNat_dvd_iff_le hn).mp (four_dvd_sub_five hm)
  have hhi : ¬3 ≤ padicValNat 2 (n - 1) := fun h ↦
    eight_not_dvd_sub_five hm ((padicValNat_dvd_iff 3 (n - 1)).mpr (Or.inr h))
  exact Nat.le_antisymm (Nat.le_of_lt_succ (Nat.lt_of_not_ge hhi)) hlo

/-- The Jacobi symbol of two is minus one for a modulus five modulo eight.
The supplementary character formula evaluates the remainder without assuming primality. -/
theorem jacobi_two_five {n : ℕ} (hm : n % 8 = 5) : jacobiSym 2 n = -1 := by
  rw [jacobiSym.at_two (mod_eight_five_data hm).2.1, ZMod.χ₈_nat_eq_if_mod_eight]
  norm_num only [hm, Nat.odd_iff.mp (mod_eight_five_data hm).2.1, ite_false, or_self]

/-- The Jacobi symbol of minus one is one for a modulus five modulo eight.
The one-modulo-four character is used to exclude an odd-power minus-one stage. -/
theorem jacobi_neg_one_five {n : ℕ} (hm : n % 8 = 5) : jacobiSym (-1) n = 1 := by
  rw [jacobiSym.at_neg_one (mod_eight_five_data hm).2.1,
    ZMod.χ₄_nat_one_mod_four (mod_eight_five_data hm).2.2]

/-- An odd power of two cannot equal one modulo a modulus five modulo eight.
Jacobi is unchanged under an odd exponent, while the symbol of one differs.
This excludes the initial-one Strong MR branch for the canonical odd part. -/
theorem odd_power_ne_one {n e : ℕ} (hm : n % 8 = 5) (he : Odd e) : (2 : ZMod n) ^ e ≠ 1 := by
  intro hp
  have hj :=
    jacobi_cast_eq n ((2 : ℤ) ^ e) 1
      (by simpa only [Int.cast_pow, Int.cast_ofNat, Int.cast_one] using hp)
  rw [jacobi_odd_pow n 2 e he, jacobi_two_five hm, jacobiSym.one_left] at hj
  norm_num only at hj

/-- An odd power of two cannot equal minus one modulo a modulus five modulo eight.
Odd-power preservation and the supplementary sign character contradict residue equality.
This excludes the zero-index minus-one Strong MR branch. -/
theorem odd_power_ne_neg_one {n e : ℕ} (hm : n % 8 = 5) (he : Odd e) : (2 : ZMod n) ^ e ≠ -1 := by
  intro hp
  have hj :=
    jacobi_cast_eq n ((2 : ℤ) ^ e) (-1)
      (by simpa only [Int.cast_pow, Int.cast_ofNat, Int.cast_neg, Int.cast_one] using hp)
  rw [jacobi_odd_pow n 2 e he, jacobi_two_five hm, jacobi_neg_one_five hm] at hj
  norm_num only at hj

/-- For a modulus five modulo eight, n/2 is twice the odd part of n-1.
The exact valuation and canonical factorization identify the half-index exponent. -/
theorem half_index_five {n : ℕ} (hm : n % 8 = 5) : n / 2 = 2 * Nat.divMaxPow (n - 1) 2 := by
  have hd := (odd_sub_canonical_decomp (mod_eight_five_data hm).1 (mod_eight_five_data hm).2.1).2.2
  rw [twoAdic_eq_two hm] at hd
  norm_num only at hd
  have ht := odd_twice_half (mod_eight_five_data hm).1 (mod_eight_five_data hm).2.1
  nlinarith only [hd, ht]

/-- A minus-one Strong MR stage has nonzero index when n is five modulo eight.
Index zero would give an odd power of two equal to minus one, already excluded. -/
theorem minus_stage_nonzero_five {n j : ℕ} (hm : n % 8 = 5)
    (hp : (2 : ZMod n) ^ (2 ^ j * Nat.divMaxPow (n - 1) 2) = -1) : j ≠ 0 := by
  intro hz
  simp only [hz, pow_zero, one_mul] at hp
  exact
    odd_power_ne_neg_one hm
      (odd_sub_canonical_decomp (mod_eight_five_data hm).1 (mod_eight_five_data hm).2.1).2.1 hp

/-- A passing minus-one stage has index one when n is five modulo eight.
The canonical valuation gives index less than two and the Jacobi argument excludes zero. -/
theorem minus_stage_eq_one_five {n j : ℕ} (hm : n % 8 = 5) (hj : j < padicValNat 2 (n - 1))
    (hp : (2 : ZMod n) ^ (2 ^ j * Nat.divMaxPow (n - 1) 2) = -1) : j = 1 := by
  rw [twoAdic_eq_two hm] at hj
  exact
    (Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.le_of_lt_succ hj)).resolve_left
      (minus_stage_nonzero_five hm hp)

/-- A base-two Strong MR pass has half-index power minus one for n five modulo eight.
Exclude the initial-one branch and force the minus-one index to one.
This supplies the sign required by Euler-Jacobi, including composite moduli. -/
theorem half_pow_neg_one_five {n : ℕ} (hm : n % 8 = 5) (h : IsStrongMillerRabinProbablePrime n 2) :
    (2 : ZMod n) ^ (n / 2) = -1 := by
  rcases isStrongMillerRabinProbablePrime_iff_pass.mp h with hp | ⟨j, hj, hp⟩
  · exact
      False.elim
        (odd_power_ne_one hm
          (odd_sub_canonical_decomp (mod_eight_five_data hm).1 (mod_eight_five_data hm).2.1).2.1 hp)
  · simpa only [minus_stage_eq_one_five hm hj (by simpa only [Nat.cast_ofNat] using hp), pow_one,
      half_index_five hm, Nat.cast_ofNat] using hp

/-- Base-two Strong MR implies Euler-Jacobi for a modulus five modulo eight.
The half-index power and the Jacobi symbol of two are both minus one.
This is the arithmetic basis of the additional conditional omission branch. -/
theorem euler_of_strong_five {n : ℕ} (hm : n % 8 = 5) (h : IsStrongMillerRabinProbablePrime n 2) :
    IsEulerJacobiProbablePrimeInt n 2 := by
  simp only [IsEulerJacobiProbablePrimeInt, Int.cast_ofNat, jacobi_two_five hm, Int.cast_neg,
    Int.cast_one]
  exact half_pow_neg_one_five hm h

/-- Every signed power of two passes Euler after MR for n five modulo eight.
Power closure and negation closure include exponent zero and negative Q.
The result supplies the executable and paper-specification consumers. -/
theorem euler_signed_two_power_five {n : ℕ} (hm : n % 8 = 5)
    (h : IsStrongMillerRabinProbablePrime n 2) {Q : ℤ} (k : ℕ)
    (hQ : Q = (2 : ℤ) ^ k ∨ Q = -(2 : ℤ) ^ k) : IsEulerJacobiProbablePrimeInt n Q := by
  have he := euler_pow (euler_of_strong_five hm h) k
  rcases hQ with hQ | hQ
  · exact hQ ▸ he
  · exact hQ ▸ euler_neg (mod_eight_five_data hm).2.1 he

/-- The shared strengthened evaluator needs only Strong and V on this MR-certified branch.
For n five modulo eight and signed two-power Q, the Euler flag is true.
The equality justifies omitting its computation from the conditional entry. -/
theorem strengthened_without_euler_five {n : ℕ} (hm : n % 8 = 5)
    (h : IsStrongMillerRabinProbablePrime n 2) (param : LucasParams) (k : ℕ)
    (hQ : param.Q = (2 : ℤ) ^ k ∨ param.Q = -(2 : ℤ) ^ k) :
    strengthenedLucasSharedEulerValid n param =
      (strongLucasWithParams n param.D param.P param.Q &&
        lucasVWithParams n param.D param.P param.Q) := by
  have he := eulerJacobiWithIntBase_eq_true_iff.mpr (euler_signed_two_power_five hm h k hQ)
  rw [strengthenedLucasSharedEulerValid_eq, strengthenedLucasSharedEuler_eq, he, Bool.and_true]

/-- The paper conditions reduce to Strong and terminal V on this MR-certified branch.
For n five modulo eight and signed two-power Q, multiplied Euler follows without cancellation.
This is the independent specification consumer of the conditional omission proof. -/
theorem bfw_without_euler_five {n : ℕ} (hm : n % 8 = 5) (h : IsStrongMillerRabinProbablePrime n 2)
    (param : LucasParams) (k : ℕ) (hQ : param.Q = (2 : ℤ) ^ k ∨ param.Q = -(2 : ℤ) ^ k) :
    BFWLucasConditions n param ↔
      IsStrongLucasProbablePrime n param ∧
        lucasVZMod n param.P param.Q (n + 1) = 2 * (param.Q : ZMod n) := by
  have he := multiplied_euler (mod_eight_five_data hm).2.1 (euler_signed_two_power_five hm h k hQ)
  simp only [BFWLucasConditions, he, and_true]

end PseudoPrime.PrimeTest.EulerRedundancy
