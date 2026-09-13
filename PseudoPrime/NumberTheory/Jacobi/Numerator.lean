/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.NumberTheory.Factorization
import PseudoPrime.NumberTheory.Jacobi.Basic
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.FieldTheory.Finite.Basic

/-!
# CRT construction of Jacobi numerators

For an odd nonsquare modulus, this file selects a prime factor of odd multiplicity and constructs
a natural number that is a quadratic nonresidue at that prime and `1` at every other prime factor.
-/

namespace PseudoPrime.NumberTheory

/-- Distinct members of a natural number's prime-factor finset are pairwise coprime. -/
theorem primeFactors_pairwise_coprime (r : ℕ) :
    Set.Pairwise (↑r.primeFactors : Set ℕ) (Function.onFun Nat.Coprime fun p => p) := by
  intro p hp q hq hpq
  exact
    (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp) (Nat.prime_of_mem_primeFactors hq)).mpr
      hpq

/--
For an odd nonsquare `r`, there is a CRT representative below the radical of `r` which is a
quadratic nonresidue at one odd-multiplicity prime factor and is `1` at all other prime factors.
-/
theorem exists_crt_residue_for_odd_factorization {r : ℕ} (hrodd : Odd r) (hns : ¬IsSquare r) :
    ∃ p₀ u a : ℕ,
      p₀ ∈ r.primeFactors ∧
        Odd (r.factorization p₀) ∧
        jacobiSym u p₀ = -1 ∧
        (∀ p ∈ r.primeFactors, a ≡ if p = p₀ then u else 1 [MOD p]) ∧
        a < ∏ p ∈ r.primeFactors, p := by
  have hr0 : r ≠ 0 := by
    have hrmod : r % 2 = 1 := Nat.odd_iff.mp hrodd
    omega
  obtain ⟨p₀, hp₀mem, hp₀odd⟩ := exists_prime_odd_factorization_of_not_square hr0 hns
  have hp₀prime : p₀.Prime := Nat.prime_of_mem_primeFactors hp₀mem
  have hp₀dvd : p₀ ∣ r := (Nat.mem_primeFactors.mp hp₀mem).2.1
  have hp₀ne2 : p₀ ≠ 2 := by
    intro hp₀two
    subst p₀
    have hreven : Even r := even_iff_two_dvd.mpr hp₀dvd
    exact (Nat.not_odd_iff_even.mpr hreven) hrodd
  let _ : Fact p₀.Prime := ⟨hp₀prime⟩
  obtain ⟨z, hz⟩ :=
    FiniteField.exists_nonsquare (F := ZMod p₀) ((ZMod.ringChar_zmod_n p₀).substr hp₀ne2)
  have hzvalue : jacobiSym z.val p₀ = -1 := by
    apply ZMod.nonsquare_iff_jacobiSym_eq_neg_one.mpr
    simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using hz
  let residue : ℕ → ℕ := fun p => if p = p₀ then z.val else 1
  have hnonzero : ∀ p ∈ r.primeFactors, (fun p => p) p ≠ 0 := by
    intro p hp
    exact (Nat.prime_of_mem_primeFactors hp).ne_zero
  let a :=
    Nat.chineseRemainderOfFinset residue (fun p => p) r.primeFactors hnonzero
      (primeFactors_pairwise_coprime r)
  have hacong : ∀ p ∈ r.primeFactors, a ≡ residue p [MOD p] := by
    intro p hp
    exact a.prop p hp
  have halt : a < ∏ p ∈ r.primeFactors, p := by
    exact
      Nat.chineseRemainderOfFinset_lt_prod residue (fun p => p) hnonzero
        (primeFactors_pairwise_coprime r)
  exact ⟨p₀, z.val, a, hp₀mem, hp₀odd, hzvalue, hacong, halt⟩

namespace Internal

/-- The Jacobi symbol distributes over a finite product in its denominator. -/
theorem jacobi_finset_prod_right (a : ℤ) (s : Finset ℕ) (f : ℕ → ℕ) (hf : ∀ p ∈ s, f p ≠ 0) :
    jacobiSym a (∏ p ∈ s, f p) = ∏ p ∈ s, jacobiSym a (f p) := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, jacobiSym.one_right]
  | @insert p s hp ih =>
    have hpne : f p ≠ 0 := hf p (Finset.mem_insert_self p s)
    have hsne : ∏ q ∈ s, f q ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun q hq => hf q (Finset.mem_insert_of_mem hq)
    rw [Finset.prod_insert hp, Finset.prod_insert hp, jacobiSym.mul_right' a hpne hsne]
    exact congrArg (jacobiSym a (f p) * ·) (ih fun q hq => hf q (Finset.mem_insert_of_mem hq))

end Internal

/-- Every nonzero odd nonsquare has a natural numerator with Jacobi value `-1`. -/
theorem exists_nat_neg_one_numerator {r : ℕ} (hrodd : Odd r) (hns : ¬IsSquare r) :
    ∃ a : ℕ, jacobiSym a r = -1 := by
  have hr0 : r ≠ 0 := by
    have hrmod : r % 2 = 1 := Nat.odd_iff.mp hrodd
    omega
  obtain ⟨p₀, u, a, hp₀mem, hp₀odd, huvalue, hacong, _⟩ :=
    exists_crt_residue_for_odd_factorization hrodd hns
  have hlocal : ∀ p ∈ r.primeFactors, jacobiSym a p = if p = p₀ then -1 else 1 := by
    intro p hp
    have hc := hacong p hp
    change a % p = (if p = p₀ then u else 1) % p at hc
    have hcint : (a : ℤ) % p = ((if p = p₀ then u else 1 : ℕ) : ℤ) % p := by exact_mod_cast hc
    rw [jacobiSym.mod_left' hcint]
    split
    · subst p
      exact huvalue
    · exact jacobiSym.one_left p
  refine ⟨a, ?_⟩
  rw [Nat.prod_primeFactors_pow_factorization hr0,
    Internal.jacobi_finset_prod_right _ _ _
      (fun p hp => pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero),
    Finset.prod_eq_single p₀]
  · rw [jacobiSym.pow_right, hlocal p₀ hp₀mem]
    rw [ite_eq_left rfl]
    exact (Odd.neg_one_pow hp₀odd : (-1 : ℤ) ^ r.factorization p₀ = -1)
  · intro p hp hpne
    rw [jacobiSym.pow_right, hlocal p hp, ite_eq_right hpne]
    exact one_pow _
  · exact fun hp₀not => (hp₀not hp₀mem).elim

/-- Every odd nonsquare modulus has a residue-class representative of Jacobi value `-1`. -/
theorem oddNonsquareHasNegOneNumerator {r : ℕ} (hrodd : Odd r) (hns : ¬IsSquare r) :
    ∃ a : ZMod r, jacobiSym a.val r = -1 := by
  obtain ⟨a, havalue⟩ := exists_nat_neg_one_numerator hrodd hns
  refine ⟨(a : ZMod r), ?_⟩
  rw [ZMod.val_natCast]
  have hmod : (((a % r : ℕ) : ℤ) % r) = (a : ℤ) % r := by
    simp only [Int.natCast_emod]
    rw [Int.emod_emod]
  rw [jacobiSym.mod_left' hmod]
  exact havalue

end PseudoPrime.NumberTheory
