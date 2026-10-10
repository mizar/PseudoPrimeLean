/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.DirichletCharacter
public import Mathlib.NumberTheory.LegendreSymbol.ZModChar
public import PseudoPrime.NumberTheory.JacobiCharacter
public import PseudoPrime.NumberTheory.JacobiCongruence
public import Mathlib.NumberTheory.FundamentalDiscriminant

/-!
# Conductors of quadratic Dirichlet characters

Certify the complex quadratic characters of conductors four and eight. At odd squarefree
levels, the Jacobi numerator character is primitive; quadratic reciprocity and the law
at two give its negative-discriminant values. These evaluations accompany primitivity
and odd parity when constructing a character for a negative odd fundamental discriminant.
-/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- A unit on which a character is not one separates its level from every proper factor level.
Factoring through any proper divisor would send that unit to one, contradicting its value.
Thus the conductor equals the level. This criterion certifies the small two-primary
quadratic characters. -/
private theorem primitive_of_separating_residue {R : Type} [CommMonoidWithZero R] {n a : ℕ}
    (χ : DirichletCharacter R n) (hcop : Nat.Coprime a n)
    (hproper : ∀ d, d ∣ n → d ≠ n → a ≡ 1 [MOD d]) (hv : χ (a : ℤ) ≠ 1) : χ.IsPrimitive := by
  by_contra h
  apply hv
  exact
    factorsThrough_apply_eq_one_of_one_modEq (DirichletCharacter.factorsThrough_conductor χ)
      (hproper χ.conductor (DirichletCharacter.conductor_dvd_level χ) h) hcop

/-- The complex-valued Jacobi numerator character at an odd level `n`.
Its value on an integer `a` is the complex cast of the Jacobi symbol `(a | n)`.
It supplies the character attached to a negative odd fundamental discriminant. -/
def complexJacobiNumeratorCharacter (n : ℕ) (hn : Odd n) : DirichletCharacter ℂ n :=
  (jacobiNumeratorCharacter n hn).ringHomComp (Int.castRingHom ℂ)

/-- The Jacobi numerator character at an odd squarefree level is primitive.
A proper conductor misses a prime factor; a CRT residue is one modulo the conductor
but has Jacobi symbol minus one and is coprime to the full level.
This contradicts the factor-through evaluation at that residue. -/
theorem complexJacobiNumeratorCharacter_isPrimitive (n : ℕ) (hn : Odd n) (hsq : Squarefree n) :
    (complexJacobiNumeratorCharacter n hn).IsPrimitive := by
  let χ := complexJacobiNumeratorCharacter n hn
  change χ.conductor = n
  apply Nat.dvd_antisymm (DirichletCharacter.conductor_dvd_level χ)
  by_contra hnot
  obtain ⟨a, _haodd, ha, hj, hcop⟩ :=
    exists_nat_odd_one_modEq_and_jacobiSym_eq_neg_one_coprime hn hsq
      (DirichletCharacter.conductor_dvd_level χ) hnot (Odd.pos hn)
  have hone :=
    factorsThrough_apply_eq_one_of_one_modEq (DirichletCharacter.factorsThrough_conductor χ) ha hcop
  have hval : χ (a : ℤ) = (-1 : ℂ) := by
    change (jacobiNumeratorCharacter n hn ((a : ℤ) : ZMod n) : ℂ) = -1
    rw [Int.cast_natCast, jacobiNumeratorCharacter_apply_natCast, hj]
    norm_num only
  rw [hval] at hone
  norm_num only at hone

/-- Evaluation of the complex Jacobi numerator character on any integer is its Jacobi symbol.
Reduce the integer modulo the level and use the modular invariance of the Jacobi symbol.
This evaluation formula also determines parity at minus one. -/
theorem complexJacobiNumeratorCharacter_apply_int (n : ℕ) (hn : Odd n) (a : ℤ) :
    complexJacobiNumeratorCharacter n hn (a : ZMod n) = (jacobiSym a n : ℂ) := by
  let : NeZero n := ⟨(Odd.pos hn).ne'⟩
  change (jacobiSym ((a : ZMod n).val) n : ℂ) = _
  congr 1
  apply jacobiSym.mod_left'
  rw [ZMod.val_intCast, Int.emod_emod]

/-- At an odd level congruent to three modulo four, the Jacobi numerator character is odd.
The supplementary law at minus one gives value minus one.
This is the parity required by a negative odd quadratic discriminant. -/
theorem complexJacobiNumeratorCharacter_odd (n : ℕ) (hn : Odd n) (hmod : n % 4 = 3) :
    (complexJacobiNumeratorCharacter n hn).Odd := by
  change complexJacobiNumeratorCharacter n hn (-1 : ZMod n) = -1
  have h := complexJacobiNumeratorCharacter_apply_int n hn (-1)
  rw [jacobiSym.at_neg_one hn, ZMod.χ₄_nat_three_mod_four hmod] at h
  simpa only [Int.cast_neg, Int.cast_one] using h

/-- The absolute value of a negative odd fundamental discriminant is squarefree.
Use the integer squarefree characterization of fundamental discriminants;
the branch divisible by four contradicts oddness. -/
private theorem negative_fundamental_odd_squarefree (n : ℕ) (hn : Odd n)
    (hf : Int.IsFundamentalDiscr (-(n : ℤ))) : Squarefree n := by
  rcases Int.isFundamentalDiscr_iff_squarefree.mp hf with ⟨_hm, hs⟩ | ⟨hm, _hs, _hr⟩
  · have h := Int.squarefree_natAbs.mpr hs
    simpa only [Int.natAbs_neg, Int.natAbs_natCast] using h
  · have h4 : (4 : ℤ) ∣ -(n : ℤ) := Int.dvd_iff_emod_eq_zero.mpr hm
    have h2 : (2 : ℤ) ∣ (n : ℤ) :=
      dvd_trans (show (2 : ℤ) ∣ 4 from by norm_num only) (dvd_neg.mp h4)
    have h2n : 2 ∣ n := by exact_mod_cast h2
    exact False.elim (hn.not_two_dvd_nat h2n)

/-- The absolute value of a negative odd fundamental discriminant is three modulo four.
Its only other odd residue would make the negative discriminant three modulo four,
contradicting the discriminant congruence condition. -/
private theorem negative_fundamental_odd_mod_four (n : ℕ) (hn : Odd n)
    (hf : Int.IsFundamentalDiscr (-(n : ℤ))) : n % 4 = 3 := by
  rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hn) with h1 | h3
  · have hm := hf.emod_four_eq_zero_or_one
    have hrem : (n : ℤ) % 4 = 1 := by
      change (n : ℤ) % ((4 : ℕ) : ℤ) = 1
      rw [← Int.natCast_emod, h1]
      norm_num only
    have h4 : ¬(4 : ℤ) ∣ (n : ℤ) := by
      intro h
      have hz := Int.emod_eq_zero_of_dvd h
      rw [hrem] at hz
      norm_num only at hz
    simp only [Int.neg_emod, ite_eq_right h4, hrem] at hm
    norm_num only at hm
    exact False.elim (hm.elim id id)
  · exact h3

/-- The complex Jacobi numerator character takes values only in zero, one and minus one.
Transfer the Jacobi symbol trichotomy through the integer-to-complex ring homomorphism.
This certifies that the constructed primitive character is quadratic. -/
theorem complexJacobiNumeratorCharacter_isQuadratic (n : ℕ) (hn : Odd n) :
    (complexJacobiNumeratorCharacter n hn).IsQuadratic := by
  have h : (jacobiNumeratorCharacter n hn).IsQuadratic := by
    intro a
    exact jacobiSym.trichotomy a.val n
  exact h.comp (Int.castRingHom ℂ)

/-- A negative odd fundamental discriminant supplies a primitive odd quadratic character
whose exact conductor is its absolute value. Construct the Jacobi numerator character,
then use squarefreeness for primitivity and the residue modulo four for odd parity. -/
theorem exists_primitive_odd_quadratic_character_of_negative_fundamental (n : ℕ) (hn : Odd n)
    (hf : Int.IsFundamentalDiscr (-(n : ℤ))) :
    ∃ χ : DirichletCharacter ℂ n, χ.IsPrimitive ∧ χ.IsQuadratic ∧ χ.Odd := by
  refine
    ⟨complexJacobiNumeratorCharacter n hn, ?_, complexJacobiNumeratorCharacter_isQuadratic n hn, ?_⟩
  · exact
      complexJacobiNumeratorCharacter_isPrimitive n hn (negative_fundamental_odd_squarefree n hn hf)
  · exact complexJacobiNumeratorCharacter_odd n hn (negative_fundamental_odd_mod_four n hn hf)

/-- The residue three is one modulo every proper divisor of four.
Check the finite divisor possibilities in the kernel. This residue detects conductor four. -/
private theorem three_modEq_one_of_proper_dvd_four {d : ℕ} (hd : d ∣ 4) (hne : d ≠ 4) :
    3 ≡ 1 [MOD d] := by
  have hle : d ≤ 4 := Nat.le_of_dvd (by norm_num only) hd
  have hc : ∀ c : Fin 5, c.val ∣ 4 → c.val ≠ 4 → 3 ≡ 1 [MOD c.val] := by decide
  exact hc ⟨d, Nat.lt_succ_of_le hle⟩ hd hne

/-- The residue five is one modulo every proper divisor of eight.
Check the finite divisor possibilities in the kernel. This residue detects conductor eight. -/
private theorem five_modEq_one_of_proper_dvd_eight {d : ℕ} (hd : d ∣ 8) (hne : d ≠ 8) :
    5 ≡ 1 [MOD d] := by
  have hle : d ≤ 8 := Nat.le_of_dvd (by norm_num only) hd
  have hc : ∀ c : Fin 9, c.val ∣ 8 → c.val ≠ 8 → 5 ≡ 1 [MOD c.val] := by decide
  exact hc ⟨d, Nat.lt_succ_of_le hle⟩ hd hne

/-- The complex character induced by the quadratic character modulo four is primitive.
Its value at three is minus one, whereas every proper factor level would give one.
This supplies the two-primary character for negative quadratic discriminants. -/
theorem complexChiFour_isPrimitive :
    DirichletCharacter.IsPrimitive (ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)) := by
  apply primitive_of_separating_residue (a := 3)
  · norm_num only
  · exact fun _ hd hne => three_modEq_one_of_proper_dvd_four hd hne
  · change ((-1 : ℤ) : ℂ) ≠ 1
    norm_num only

/-- The complex character induced by the even quadratic character `χ₈` modulo eight is primitive.
The unit five has value minus one and is one at every proper factor level.
This certifies its exact conductor for two-primary quadratic character products. -/
theorem complexChiEight_isPrimitive :
    DirichletCharacter.IsPrimitive (ZMod.χ₈.ringHomComp (Int.castRingHom ℂ)) := by
  apply primitive_of_separating_residue (a := 5)
  · norm_num only
  · exact fun _ hd hne => five_modEq_one_of_proper_dvd_eight hd hne
  · change ((-1 : ℤ) : ℂ) ≠ 1
    norm_num only

/-- The complex character induced by the odd quadratic character `χ₈'` modulo eight is primitive.
Its value at five excludes all proper factor levels and gives exact conductor eight.
This supplies the other parity choice for two-primary quadratic character products. -/
theorem complexChiEightPrime_isPrimitive :
    DirichletCharacter.IsPrimitive (ZMod.χ₈'.ringHomComp (Int.castRingHom ℂ)) := by
  apply primitive_of_separating_residue (a := 5)
  · norm_num only
  · exact fun _ hd hne => five_modEq_one_of_proper_dvd_eight hd hne
  · change ((-1 : ℤ) : ℂ) ≠ 1
    norm_num only

/-- The cross-level product of two quadratic complex characters is quadratic.
Change of level preserves the square-one identity, and multiplication preserves it
because the character group is commutative. This certifies the combined odd and
two-primary parts. -/
private theorem quadratic_mul {n m : ℕ} (χ : DirichletCharacter ℂ n) (ψ : DirichletCharacter ℂ m)
    (hχ : χ.IsQuadratic) (hψ : ψ.IsQuadratic) : (DirichletCharacter.mul χ ψ).IsQuadratic := by
  rw [MulChar.isQuadratic_iff_sq_eq_one, DirichletCharacter.mul, mul_pow]
  rw [← map_pow, ← map_pow, hχ.sq_eq_one, hψ.sq_eq_one, map_one, map_one, one_mul]

/-- An odd squarefree integer `n` supplies a primitive quadratic character of conductor `4n`.
Multiply its Jacobi numerator character by the primitive character modulo four.
Their conductors are coprime, so the product has exact conductor `4n`.
This constructs the character for the four-times-odd part of the discriminant classification. -/
theorem exists_primitive_quadratic_character_four_mul (n : ℕ) (hn : Odd n) (hsq : Squarefree n) :
    ∃ χ : DirichletCharacter ℂ (4 * n), χ.IsPrimitive ∧ χ.IsQuadratic := by
  let : NeZero n := ⟨(Odd.pos hn).ne'⟩
  have hc : Nat.Coprime 4 n := by
    have h := hn.coprime_two_left.pow_left 2
    norm_num only at h
    exact h
  have h : ∃ χ : DirichletCharacter ℂ (Nat.lcm 4 n), χ.IsPrimitive ∧ χ.IsQuadratic := by
    refine
      ⟨DirichletCharacter.mul (ZMod.χ₄.ringHomComp (Int.castRingHom ℂ))
          (complexJacobiNumeratorCharacter n hn),
        ?_, ?_⟩
    · exact
        primitive_mul_of_coprime _ _ complexChiFour_isPrimitive
          (complexJacobiNumeratorCharacter_isPrimitive n hn hsq) hc
    · exact
        quadratic_mul _ _ (ZMod.isQuadratic_χ₄.comp (Int.castRingHom ℂ))
          (complexJacobiNumeratorCharacter_isQuadratic n hn)
  rw [hc.lcm_eq_mul] at h
  exact h

/-- An odd squarefree integer `n` supplies a primitive quadratic character of conductor `8n`.
Multiply its Jacobi numerator character by the first primitive character modulo eight.
The coprime product formula gives conductor `8n`, and both factors are quadratic.
The parity choice for a specific negative discriminant also involves the second character
modulo eight. -/
theorem exists_primitive_quadratic_character_eight_mul (n : ℕ) (hn : Odd n) (hsq : Squarefree n) :
    ∃ χ : DirichletCharacter ℂ (8 * n), χ.IsPrimitive ∧ χ.IsQuadratic := by
  let : NeZero n := ⟨(Odd.pos hn).ne'⟩
  have hc : Nat.Coprime 8 n := by
    have h := hn.coprime_two_left.pow_left 3
    norm_num only at h
    exact h
  have h : ∃ χ : DirichletCharacter ℂ (Nat.lcm 8 n), χ.IsPrimitive ∧ χ.IsQuadratic := by
    refine
      ⟨DirichletCharacter.mul (ZMod.χ₈.ringHomComp (Int.castRingHom ℂ))
          (complexJacobiNumeratorCharacter n hn),
        ?_, ?_⟩
    · exact
        primitive_mul_of_coprime _ _ complexChiEight_isPrimitive
          (complexJacobiNumeratorCharacter_isPrimitive n hn hsq) hc
    · exact
        quadratic_mul _ _ (ZMod.isQuadratic_χ₈.comp (Int.castRingHom ℂ))
          (complexJacobiNumeratorCharacter_isQuadratic n hn)
  rw [hc.lcm_eq_mul] at h
  exact h

/-- For odd `q ≡ 3 mod 4` and odd `p`, the numerator symbol `J(p | q)`
is `J(-q | p)`. Use quadratic reciprocity in the two possible residues of `p`
modulo four and the supplementary law for minus one. Coprimality is not required,
so this also covers odd primes dividing the discriminant. -/
private theorem jacobi_negative_reciprocity {q p : ℕ} (hq : Odd q) (hmod : q % 4 = 3) (hp : Odd p) :
    jacobiSym (p : ℤ) q = jacobiSym (-(q : ℤ)) p := by
  rw [jacobiSym.neg (q : ℤ) hp]
  rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hp) with h1 | h3
  · rw [ZMod.χ₄_nat_one_mod_four h1, one_mul]
    exact jacobiSym.quadratic_reciprocity_one_mod_four h1 hq
  · rw [ZMod.χ₄_nat_three_mod_four h3, neg_one_mul]
    exact jacobiSym.quadratic_reciprocity_three_mod_four h3 hmod

/-- At every odd prime `p`, the Jacobi numerator character of an odd conductor
`q ≡ 3 mod 4` has value `legendreSym p (-q)`. Its integer evaluation and quadratic
reciprocity identify the value, including zero at primes dividing `q`.
This connects the character of a negative odd discriminant to its square class modulo `p`. -/
theorem complexJacobiNumeratorCharacter_apply_prime_negative_discr (q : ℕ) (hq : Odd q)
    (hmod : q % 4 = 3) (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    complexJacobiNumeratorCharacter q hq (p : ℕ) = (legendreSym p (-(q : ℤ)) : ℂ) := by
  have hp : Odd p := (Fact.out : p.Prime).eq_two_or_odd'.resolve_left hp2
  have h := complexJacobiNumeratorCharacter_apply_int q hq (p : ℤ)
  rw [jacobi_negative_reciprocity hq hmod hp, ← jacobiSym.legendreSym.to_jacobiSym] at h
  simpa only [Int.cast_natCast] using h

/-- At every odd level `q`, the Jacobi numerator character has value `χ₈(-q)` at two.
The supplementary law for two and evenness of the character modulo eight identify
these values for any odd `q`, without squarefreeness or fundamental-discriminant assumptions.
This supplies the dyadic character value needed by quadratic prime splitting. -/
theorem complexJacobiNumeratorCharacter_apply_two_negative_discr (q : ℕ) (hq : Odd q) :
    complexJacobiNumeratorCharacter q hq (2 : ℕ) = (ZMod.χ₈ (-(q : ℤ)) : ℂ) := by
  have h := complexJacobiNumeratorCharacter_apply_int q hq 2
  rw [jacobiSym.at_two hq] at h
  have he : ZMod.χ₈ (-(q : ℤ)) = ZMod.χ₈ (q : ℤ) :=
    (by decide : ∀ x : ZMod 8, ZMod.χ₈ (-x) = ZMod.χ₈ x) (q : ZMod 8)
  rw [he]
  simpa only [Int.cast_natCast, Int.cast_ofNat, Nat.cast_ofNat] using h

/-- A negative odd fundamental discriminant has a primitive odd quadratic character
whose values match its Legendre symbols at odd primes and its character-modulo-eight
value at two. Use the same Jacobi numerator character for primitivity, parity, and
all evaluations. This joint construction ensures that the character used in quadratic
ideal counting is the character of the actual discriminant. -/
theorem exists_primitive_character_values_of_negative_odd_fundamental (q : ℕ) (hq : Odd q)
    (hf : Int.IsFundamentalDiscr (-(q : ℤ))) :
    ∃ χ : DirichletCharacter ℂ q,
      χ.IsPrimitive ∧
        χ.IsQuadratic ∧
        χ.Odd ∧
        (∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → χ (p : ℕ) = (legendreSym p (-(q : ℤ)) : ℂ)) ∧
        χ (2 : ℕ) = (ZMod.χ₈ (-(q : ℤ)) : ℂ) := by
  refine
    ⟨complexJacobiNumeratorCharacter q hq,
      complexJacobiNumeratorCharacter_isPrimitive q hq
        (negative_fundamental_odd_squarefree q hq hf),
      complexJacobiNumeratorCharacter_isQuadratic q hq,
      complexJacobiNumeratorCharacter_odd q hq (negative_fundamental_odd_mod_four q hq hf), ?_,
      complexJacobiNumeratorCharacter_apply_two_negative_discr q hq⟩
  intro p hp hp2
  exact
    complexJacobiNumeratorCharacter_apply_prime_negative_discr q hq
      (negative_fundamental_odd_mod_four q hq hf) p hp2

end PseudoPrime.NumberTheory
