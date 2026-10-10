/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.Tactic.NormNum

/-!
# Parity of Dirichlet characters

Primitive normalization preserves evaluation at minus one. Orthogonality at that
element shows that, for modulus greater than two, half of the complex characters
are even and half are odd. These counts support parity-sensitive character averages.
-/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- Primitive normalization preserves the value at minus one for any character.
Minus one is coprime to every level, so the primitive-character evaluation formula applies.
This transports parity-dependent estimates between a character and its primitive normalization. -/
theorem primitiveCharacter_apply_neg_one {R : Type*} [CommMonoidWithZero R] {q : ℕ}
    (χ : DirichletCharacter R q) : χ.primitiveCharacter (-1) = χ (-1) := by
  have hcop : IsCoprime (-1 : ℤ) (q : ℤ) := isCoprime_one_left.neg_left
  simpa only [Int.cast_neg, Int.cast_one] using
    DirichletCharacter.primitiveCharacter_apply_of_isCoprime χ hcop

/-- A character with values in a commutative ring is even after primitive normalization
exactly when the original character is even. Rewrite the value at minus one.
This preserves the even branch when summing estimates over full-level characters. -/
theorem primitiveCharacter_even_iff {R : Type*} [CommRing R] {q : ℕ} (χ : DirichletCharacter R q) :
    χ.primitiveCharacter.Even ↔ χ.Even := by
  rw [DirichletCharacter.Even, DirichletCharacter.Even, primitiveCharacter_apply_neg_one]

/-- A character with values in a commutative ring is odd after primitive normalization
exactly when the original character is odd. Rewrite the value at minus one.
This preserves the odd branch of primitive estimates in full-level averages. -/
theorem primitiveCharacter_odd_iff {R : Type*} [CommRing R] {q : ℕ} (χ : DirichletCharacter R q) :
    χ.primitiveCharacter.Odd ↔ χ.Odd := by
  rw [DirichletCharacter.Odd, DirichletCharacter.Odd, primitiveCharacter_apply_neg_one]

/-- A complex character is not even exactly when it is odd.
Use the exhaustive parity dichotomy and the disjointness of the two branches.
This identifies the complement when partitioning finite character sums. -/
theorem dirichletCharacter_not_even_iff_odd {q : ℕ} (χ : DirichletCharacter ℂ q) :
    ¬χ.Even ↔ χ.Odd := by
  constructor
  · intro h
    exact χ.even_or_odd.resolve_left h
  · intro h
    exact h.not_even

open Classical in
/-- The sum of character values at minus one is the even count minus the odd count.
Each summand is one or minus one according to parity; split the sum over that predicate.
Orthogonality can then identify the two counts without enumerating characters. -/
theorem sum_dirichletCharacters_neg_one_eq_card_even_sub_card_odd (q : ℕ) :
    (∑ χ : DirichletCharacter ℂ q, χ (-1)) =
      ((Finset.univ.filter (fun χ : DirichletCharacter ℂ q ↦ χ.Even)).card : ℂ) -
        ((Finset.univ.filter (fun χ : DirichletCharacter ℂ q ↦ χ.Odd)).card : ℂ) := by
  have he :
    (∑ χ : DirichletCharacter ℂ q, χ (-1)) =
      ∑ χ : DirichletCharacter ℂ q, if χ.Even then (1 : ℂ) else -1 := by
    apply Finset.sum_congr rfl
    intro χ _
    by_cases hχ : χ.Even
    · rw [ite_eq_left hχ]
      exact hχ
    · rw [ite_eq_right hχ]
      exact χ.even_or_odd.resolve_left hχ
  simpa only [Finset.sum_ite, Finset.sum_const, nsmul_eq_mul, mul_neg, mul_one,
    dirichletCharacter_not_even_iff_odd, sub_eq_add_neg] using he

open Classical in
/-- For a nonzero modulus, even and odd complex character counts add to its totient.
Partition all characters by parity and use the cardinality of the full character group.
Together with equality of the two counts, this determines both averaging coefficients. -/
theorem card_even_dirichletCharacters_add_card_odd (q : ℕ) [NeZero q] :
    (Finset.univ.filter (fun χ : DirichletCharacter ℂ q ↦ χ.Even)).card +
        (Finset.univ.filter (fun χ : DirichletCharacter ℂ q ↦ χ.Odd)).card =
      q.totient := by
  have hc :=
    Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun χ : DirichletCharacter ℂ q ↦ χ.Even)
  have ht : Fintype.card (DirichletCharacter ℂ q) = q.totient :=
    Nat.card_eq_fintype_card.symm.trans
      (DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q)
  simpa only [dirichletCharacter_not_even_iff_odd, Finset.card_univ, ht] using hc

open Classical in
/-- For modulus greater than two, the even and odd complex character counts are equal.
Minus one differs from one, so orthogonality makes its character sum zero.
Take real parts of the count difference and return to natural-number equality. -/
theorem card_even_dirichletCharacters_eq_card_odd {q : ℕ} [NeZero q] (hq : 2 < q) :
    (Finset.univ.filter (fun χ : DirichletCharacter ℂ q ↦ χ.Even)).card =
      (Finset.univ.filter (fun χ : DirichletCharacter ℂ q ↦ χ.Odd)).card := by
  let : Fact (2 < q) := ⟨hq⟩
  have hz := DirichletCharacter.sum_characters_eq_zero ℂ (ZMod.neg_one_ne_one (n := q))
  rw [sum_dirichletCharacters_neg_one_eq_card_even_sub_card_odd q] at hz
  have hr := congrArg Complex.re hz
  simp only [Complex.sub_re, Complex.natCast_re, Complex.zero_re] at hr
  exact_mod_cast sub_eq_zero.mp hr

open Classical in
/-- For modulus greater than two, twice the even complex character count is its totient.
Replace the odd count by the even count in the parity partition.
This expresses the coefficient without natural-number division. -/
theorem two_mul_card_even_dirichletCharacters {q : ℕ} [NeZero q] (hq : 2 < q) :
    2 * (Finset.univ.filter (fun χ : DirichletCharacter ℂ q ↦ χ.Even)).card = q.totient := by
  have hc := card_even_dirichletCharacters_add_card_odd q
  rw [← card_even_dirichletCharacters_eq_card_odd hq] at hc
  simpa only [two_mul] using hc

open Classical in
/-- For modulus greater than two, twice the odd complex character count is its totient.
Transfer the even count identity through equality of the two parity counts.
This gives the odd coefficient in parity-sensitive finite averages. -/
theorem two_mul_card_odd_dirichletCharacters {q : ℕ} [NeZero q] (hq : 2 < q) :
    2 * (Finset.univ.filter (fun χ : DirichletCharacter ℂ q ↦ χ.Odd)).card = q.totient := by
  rw [← card_even_dirichletCharacters_eq_card_odd hq]
  exact two_mul_card_even_dirichletCharacters hq

open Classical in
/-- For modulus greater than two, summing an even value `E` and an odd value `O`
over all complex characters gives `totient/2` times each value.
Split the sum by parity and convert the two count identities to real coefficients.
This is the full-character averaging formula for parity-dependent estimates. -/
theorem sum_dirichletCharacters_parity_values {q : ℕ} [NeZero q] (hq : 2 < q) (E O : ℝ) :
    (∑ χ : DirichletCharacter ℂ q, if χ.Even then E else O) =
      (q.totient : ℝ) / 2 * E + (q.totient : ℝ) / 2 * O := by
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
  have he :
    ((Finset.univ.filter (fun χ : DirichletCharacter ℂ q ↦ χ.Even)).card : ℝ) =
      (q.totient : ℝ) / 2 := by
    have h :
      (2 : ℝ) * (Finset.univ.filter (fun χ : DirichletCharacter ℂ q ↦ χ.Even)).card =
        q.totient := by
      exact_mod_cast two_mul_card_even_dirichletCharacters hq
    linarith only [h]
  have ho :
    ((Finset.univ.filter (fun χ : DirichletCharacter ℂ q ↦ ¬χ.Even)).card : ℝ) =
      (q.totient : ℝ) / 2 := by
    simp only [dirichletCharacter_not_even_iff_odd]
    have h :
      (2 : ℝ) * (Finset.univ.filter (fun χ : DirichletCharacter ℂ q ↦ χ.Odd)).card = q.totient := by
      exact_mod_cast two_mul_card_odd_dirichletCharacters hq
    linarith only [h]
  rw [he, ho]

open Classical in
/-- For modulus greater than two, separate even and odd upper bounds on nonprincipal
complex characters sum with coefficients `totient/2 - 1` and `totient/2`.
Compare each term with its parity bound and remove the even principal character
from the full-character averaging formula. No sign assumptions on the bounds are needed.
This keeps the parity savings instead of using a common worst-case bound. -/
theorem sum_nonprincipal_dirichletCharacters_le_parity_average {q : ℕ} [NeZero q] (hq : 2 < q)
    (f : DirichletCharacter ℂ q → ℝ) {E O : ℝ} (hE : ∀ χ, χ ≠ 1 → χ.Even → f χ ≤ E)
    (hO : ∀ χ, χ ≠ 1 → χ.Odd → f χ ≤ O) :
    (∑ χ ∈ Finset.univ.erase 1, f χ) ≤ ((q.totient : ℝ) / 2 - 1) * E + (q.totient : ℝ) / 2 * O := by
  have hs :
    (∑ χ ∈ Finset.univ.erase 1, f χ) ≤
      ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), if χ.Even then E else O := by
    apply Finset.sum_le_sum
    intro χ hχ
    by_cases he : χ.Even
    · simpa only [ite_eq_left he] using hE χ (Finset.mem_erase.mp hχ).1 he
    · simpa only [ite_eq_right he] using
        hO χ (Finset.mem_erase.mp hχ).1 (χ.even_or_odd.resolve_left he)
  have hprincipal : (1 : DirichletCharacter ℂ q).Even := MulChar.one_apply isUnit_neg_one
  have heq :=
    Finset.sum_erase_add (s := Finset.univ)
      (fun χ : DirichletCharacter ℂ q ↦ if χ.Even then E else O) (Finset.mem_univ 1)
  simp only [ite_eq_left hprincipal] at heq
  have hfull := sum_dirichletCharacters_parity_values hq E O
  rw [← heq] at hfull
  linarith only [hs, hfull]

end PseudoPrime.NumberTheory
