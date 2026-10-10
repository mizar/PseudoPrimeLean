/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.QuadraticCharacterConductor
public import PseudoPrime.NumberTheory.QuadraticFieldDiscriminant

/-!
# Characters attached to negative quadratic discriminants

Construct primitive odd quadratic complex characters at every negative fundamental
discriminant, including the two-primary branches, and connect the construction to
the actual discriminant of a degree-two number field. The stronger construction
retains the Legendre-symbol evaluations at odd primes and the `χ₈` evaluation at two
on the same primitive character, for use in prime ideal splitting.
-/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- Evaluation at minus one of a cross-level product is the product of the two evaluations.
Minus one is coprime to every level, so changing levels preserves both factor values.
This identifies the parity of the constructed quadratic character. -/
private theorem mul_eval_neg_one {n m : ℕ} (χ : DirichletCharacter ℂ n)
    (ψ : DirichletCharacter ℂ m) : (DirichletCharacter.mul χ ψ) (-1) = χ (-1) * ψ (-1) := by
  have h : IsCoprime (-1 : ℤ) (Nat.lcm n m) := by
    refine ⟨-1, 0, ?_⟩
    ring
  have hχ := DirichletCharacter.changeLevel_eq_cast_of_dvd' χ (Nat.dvd_lcm_left n m) h
  have hψ := DirichletCharacter.changeLevel_eq_cast_of_dvd' ψ (Nat.dvd_lcm_right n m) h
  change
    (DirichletCharacter.changeLevel (Nat.dvd_lcm_left n m) χ) (-1) *
        (DirichletCharacter.changeLevel (Nat.dvd_lcm_right n m) ψ) (-1) =
      _
  simpa only [Int.cast_neg, Int.cast_one] using congrArg₂ (fun x y : ℂ => x * y) hχ hψ

/-- At an odd level congruent to one modulo four, the complex Jacobi numerator character
is even. Evaluate at minus one with the supplementary law and the character modulo four.
This supplies the odd part of the four-times-odd discriminant branch. -/
private theorem jacobi_even_of_mod_four_one (n : ℕ) (hn : Odd n) (hmod : n % 4 = 1) :
    (complexJacobiNumeratorCharacter n hn).Even := by
  change complexJacobiNumeratorCharacter n hn (-1 : ZMod n) = 1
  have h := complexJacobiNumeratorCharacter_apply_int n hn (-1)
  rw [jacobiSym.at_neg_one hn, ZMod.χ₄_nat_one_mod_four hmod] at h
  simpa only [Int.cast_neg, Int.cast_one] using h

/-- The complex character modulo four has value minus one at minus one.
Evaluate the finite character and its integer-to-complex cast. This gives its odd parity. -/
private theorem chiFour_neg_one : (ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)) (-1) = (-1 : ℂ) := by
  change ((-1 : ℤ) : ℂ) = -1
  norm_num only

/-- The first complex character modulo eight has value one at minus one.
Its even parity is used when the Jacobi numerator factor is odd. -/
private theorem chiEight_neg_one : (ZMod.χ₈.ringHomComp (Int.castRingHom ℂ)) (-1) = (1 : ℂ) := by
  change ((1 : ℤ) : ℂ) = 1
  norm_num only

/-- The second complex character modulo eight has value minus one at minus one.
Its odd parity is used when the Jacobi numerator factor is even. -/
private theorem chiEightPrime_neg_one :
    (ZMod.χ₈'.ringHomComp (Int.castRingHom ℂ)) (-1) = (-1 : ℂ) := by
  change ((-1 : ℤ) : ℂ) = -1
  norm_num only

/-- Combine primitive quadratic characters at coprime nonzero levels whose parity product
is minus one. The conductor product formula proves primitivity, the square-one identities
prove quadraticity, and evaluation at minus one proves oddness. Transport the least common
multiple level to the product level for the discriminant constructions. -/
private theorem primitive_odd_quadratic_product {m n : ℕ} [NeZero m] [NeZero n]
    (θ : DirichletCharacter ℂ m) (χ : DirichletCharacter ℂ n) (hθ : θ.IsPrimitive)
    (hχ : χ.IsPrimitive) (hqθ : θ.IsQuadratic) (hqχ : χ.IsQuadratic) (hc : Nat.Coprime m n)
    (hpar : θ (-1) * χ (-1) = -1) :
    ∃ η : DirichletCharacter ℂ (m * n), η.IsPrimitive ∧ η.IsQuadratic ∧ η.Odd := by
  have h : ∃ η : DirichletCharacter ℂ (Nat.lcm m n), η.IsPrimitive ∧ η.IsQuadratic ∧ η.Odd := by
    refine ⟨DirichletCharacter.mul θ χ, primitive_mul_of_coprime θ χ hθ hχ hc, ?_, ?_⟩
    · rw [MulChar.isQuadratic_iff_sq_eq_one, DirichletCharacter.mul, mul_pow]
      rw [← map_pow, ← map_pow, hqθ.sq_eq_one, hqχ.sq_eq_one, map_one, map_one, one_mul]
    · change (DirichletCharacter.mul θ χ) (-1) = -1
      rw [mul_eval_neg_one]
      exact hpar
  rw [hc.lcm_eq_mul] at h
  exact h

/-- For odd squarefree `n` congruent to one modulo four, construct a primitive odd quadratic
character of conductor `4n`. Multiply the character modulo four by the Jacobi numerator
character: the former is odd and the latter is even. -/
private theorem four_mul_odd_character (n : ℕ) (hn : Odd n) (hsq : Squarefree n)
    (hmod : n % 4 = 1) :
    ∃ χ : DirichletCharacter ℂ (4 * n), χ.IsPrimitive ∧ χ.IsQuadratic ∧ χ.Odd := by
  let : NeZero n := ⟨(Odd.pos hn).ne'⟩
  apply
    primitive_odd_quadratic_product (ZMod.χ₄.ringHomComp (Int.castRingHom ℂ))
      (complexJacobiNumeratorCharacter n hn) complexChiFour_isPrimitive
      (complexJacobiNumeratorCharacter_isPrimitive n hn hsq) (ZMod.isQuadratic_χ₄.comp _)
      (complexJacobiNumeratorCharacter_isQuadratic n hn)
  · have h := hn.coprime_two_left.pow_left 2
    norm_num only at h
    exact h
  · rw [chiFour_neg_one, jacobi_even_of_mod_four_one n hn hmod]
    ring

/-- For odd squarefree `n`, construct a primitive odd quadratic character of conductor `8n`.
If the Jacobi numerator character is even, use the second character modulo eight;
if it is odd, use the first. Coprime conductor multiplication preserves primitivity
and both products have value minus one at minus one. -/
private theorem eight_mul_odd_character (n : ℕ) (hn : Odd n) (hsq : Squarefree n) :
    ∃ χ : DirichletCharacter ℂ (8 * n), χ.IsPrimitive ∧ χ.IsQuadratic ∧ χ.Odd := by
  let : NeZero n := ⟨(Odd.pos hn).ne'⟩
  let χ := complexJacobiNumeratorCharacter n hn
  have hp : χ.IsPrimitive := complexJacobiNumeratorCharacter_isPrimitive n hn hsq
  have hq : χ.IsQuadratic := complexJacobiNumeratorCharacter_isQuadratic n hn
  have hc : Nat.Coprime 8 n := by
    have h := hn.coprime_two_left.pow_left 3
    norm_num only at h
    exact h
  rcases χ.even_or_odd with he | ho
  · apply
      primitive_odd_quadratic_product (ZMod.χ₈'.ringHomComp (Int.castRingHom ℂ)) χ
        complexChiEightPrime_isPrimitive hp (ZMod.isQuadratic_χ₈'.comp _) hq hc
    rw [chiEightPrime_neg_one, he]
    ring
  · apply
      primitive_odd_quadratic_product (ZMod.χ₈.ringHomComp (Int.castRingHom ℂ)) χ
        complexChiEight_isPrimitive hp (ZMod.isQuadratic_χ₈.comp _) hq hc
    rw [chiEight_neg_one, ho]
    ring

/-- The residue modulo four of a negative natural number is zero for multiples of four,
and otherwise four minus the natural residue. Translate the integer negation formula
using the compatibility of natural casts with remainders. -/
private theorem negative_nat_mod_four (n : ℕ) :
    (-(n : ℤ)) % 4 = if n % 4 = 0 then 0 else (4 : ℤ) - ((n % 4 : ℕ) : ℤ) := by
  simp only [Int.neg_emod, Int.dvd_iff_emod_eq_zero]
  have hrem : (n : ℤ) % 4 = ((n % 4 : ℕ) : ℤ) := by exact (Int.natCast_emod n 4).symm
  rw [hrem]
  norm_num only [Nat.cast_eq_zero]

/-- A natural number congruent to one modulo four is odd.
Reduce its residue modulo two using divisibility of four by two. -/
private theorem odd_of_mod_four_one (n : ℕ) (h : n % 4 = 1) : Odd n := by
  apply Nat.odd_iff.mpr
  rw [← Nat.mod_mod_of_dvd n (show 2 ∣ 4 from by norm_num only), h]

/-- If a negative natural number is one modulo four, the natural number is three modulo four.
Check its four possible remainder values. This selects the odd discriminant branch. -/
private theorem negative_mod_four_one (n : ℕ) (h : (-(n : ℤ)) % 4 = 1) : n % 4 = 3 := by
  rw [negative_nat_mod_four] at h
  have hl := Nat.mod_lt n (show 0 < 4 from by norm_num only)
  interval_cases hn : n % 4
  · norm_num only [hn, ite_true] at h
  · norm_num only [hn, ite_false] at h
  · norm_num only [hn, ite_false] at h
  · rfl

/-- If a negative natural number is two or three modulo four, its positive value is two
or one modulo four. Check the four possible residues. This splits the even discriminant
branch into a four-times-odd or an eight-times-odd conductor. -/
private theorem negative_mod_four_two_or_three (n : ℕ)
    (h : (-(n : ℤ)) % 4 = 2 ∨ (-(n : ℤ)) % 4 = 3) : n % 4 = 2 ∨ n % 4 = 1 := by
  rw [negative_nat_mod_four] at h
  have hl := Nat.mod_lt n (show 0 < 4 from by norm_num only)
  interval_cases hn : n % 4
  · norm_num only [hn, ite_true, false_or] at h
  · exact Or.inr rfl
  · exact Or.inl rfl
  · norm_num only [hn, ite_false, false_or] at h

/-- A natural number congruent to three modulo four is odd.
Reduce the remainder modulo two. This applies to the absolute value of an odd
negative discriminant. -/
private theorem odd_of_mod_four_three (n : ℕ) (h : n % 4 = 3) : Odd n := by
  apply Nat.odd_iff.mpr
  rw [← Nat.mod_mod_of_dvd n (show 2 ∣ 4 from by norm_num only), h]

/-- Every negative fundamental discriminant has a primitive odd quadratic character
whose conductor is its absolute value. The integer squarefree characterization gives
an odd branch, a four-times-odd branch, or an eight-times-odd branch. Use the Jacobi
numerator character in the first, and the parity-adjusted two-primary product in the
other two. No restriction to odd or prime discriminants is imposed. -/
theorem exists_primitive_odd_quadratic_character_of_fundamental_discr (q : ℕ)
    (hf : Int.IsFundamentalDiscr (-(q : ℤ))) :
    ∃ χ : DirichletCharacter ℂ q, χ.IsPrimitive ∧ χ.IsQuadratic ∧ χ.Odd := by
  rcases Int.isFundamentalDiscr_iff_squarefree.mp hf with ⟨hm, _hs⟩ | ⟨hm, hs, hr⟩
  · have hqodd := odd_of_mod_four_three q (negative_mod_four_one q hm)
    exact exists_primitive_odd_quadratic_character_of_negative_fundamental q hqodd hf
  · have hdZ : (4 : ℤ) ∣ (q : ℤ) := dvd_neg.mp (Int.dvd_iff_emod_eq_zero.mpr hm)
    have hd : 4 ∣ q := by exact_mod_cast hdZ
    obtain ⟨n, rfl⟩ := hd
    have hquot : (-(4 * n : ℕ) : ℤ) / 4 = -(n : ℤ) := by
      simp only [Nat.cast_mul, Nat.cast_ofNat]
      rw [← Int.mul_neg, Int.mul_ediv_cancel_left _ (show (4 : ℤ) ≠ 0 from by norm_num only)]
    rw [hquot] at hs hr
    have hsq : Squarefree n := by
      have h := Int.squarefree_natAbs.mpr hs
      simpa only [Int.natAbs_neg, Int.natAbs_natCast] using h
    rcases negative_mod_four_two_or_three n hr with h2 | h1
    · have hn2 : n % 2 = 0 := by rw [← Nat.mod_mod_of_dvd n (show 2 ∣ 4 from by norm_num only), h2]
      have hdiv : 2 ∣ n := even_iff_two_dvd.mp (Nat.even_iff.mpr hn2)
      obtain ⟨m, rfl⟩ := hdiv
      have hmOdd : Odd m := by
        apply Nat.odd_iff.mpr
        have hh : 2 * (m % 2) = 2 := by
          simpa only [show (4 : ℕ) = 2 * 2 from rfl, Nat.mul_mod_mul_left] using h2
        exact Nat.eq_of_mul_eq_mul_left (show 0 < (2 : ℕ) from by norm_num only) hh
      have hmSq : Squarefree m := hsq.squarefree_of_dvd (Nat.dvd_mul_left m 2)
      rw [show 4 * (2 * m) = 8 * m by ring]
      exact eight_mul_odd_character m hmOdd hmSq
    · exact four_mul_odd_character n (odd_of_mod_four_one n h1) hsq h1

/-- A degree-two number field of discriminant `-q` has a primitive odd quadratic character
of exact conductor `q`. Prove that its actual discriminant is fundamental, then apply
the construction covering all parity branches. This supplies the character existence
needed by the quadratic Dedekind factorization; the ideal coefficient identity is separate. -/
theorem exists_primitive_odd_quadratic_character_of_discr (q : ℕ) (K : Type) [Field K]
    [NumberField K] (hdeg : Module.finrank ℚ K = 2) (hd : NumberField.discr K = -(q : ℤ)) :
    ∃ χ : DirichletCharacter ℂ q, χ.IsPrimitive ∧ χ.IsQuadratic ∧ χ.Odd := by
  apply exists_primitive_odd_quadratic_character_of_fundamental_discr q
  rw [← hd]
  exact quadratic_discr_isFundamental K hdeg

/-- At a natural residue coprime to the least common multiple of two levels, the
cross-level product evaluates as the product of the original character values.
Change of level preserves both values on this unit. This supplies the evaluation
formula retained in the discriminant character construction. -/
private theorem mul_eval_coprime_nat {n m : ℕ} (χ : DirichletCharacter ℂ n)
    (ψ : DirichletCharacter ℂ m) (a : ℕ) (ha : Nat.Coprime a (Nat.lcm n m)) :
    (DirichletCharacter.mul χ ψ) (a : ℕ) = χ (a : ℕ) * ψ (a : ℕ) := by
  have hχ := DirichletCharacter.changeLevel_eq_cast_of_dvd' χ (Nat.dvd_lcm_left n m) ha.isCoprime
  have hψ := DirichletCharacter.changeLevel_eq_cast_of_dvd' ψ (Nat.dvd_lcm_right n m) ha.isCoprime
  change
    (DirichletCharacter.changeLevel (Nat.dvd_lcm_left n m) χ) (a : ℕ) *
        (DirichletCharacter.changeLevel (Nat.dvd_lcm_right n m) ψ) (a : ℕ) =
      _
  simpa only [Int.cast_natCast] using congrArg₂ (fun x y : ℂ ↦ x * y) hχ hψ

/-- Combine coprime primitive quadratic characters with odd parity and retain their
evaluation formula at coprime residues. Transport the least common multiple level
to the product level. This keeps primitivity and discriminant values on the same character. -/
private theorem primitive_odd_product_values {m n : ℕ} [NeZero m] [NeZero n]
    (θ : DirichletCharacter ℂ m) (χ : DirichletCharacter ℂ n) (hθ : θ.IsPrimitive)
    (hχ : χ.IsPrimitive) (hqθ : θ.IsQuadratic) (hqχ : χ.IsQuadratic) (hc : Nat.Coprime m n)
    (hpar : θ (-1) * χ (-1) = -1) :
    ∃ η : DirichletCharacter ℂ (m * n),
      η.IsPrimitive ∧
        η.IsQuadratic ∧
        η.Odd ∧ (∀ a : ℕ, Nat.Coprime a (m * n) → η (a : ℕ) = θ (a : ℕ) * χ (a : ℕ)) := by
  have h :
    ∃ η : DirichletCharacter ℂ (Nat.lcm m n),
      η.IsPrimitive ∧
        η.IsQuadratic ∧
        η.Odd ∧ (∀ a : ℕ, Nat.Coprime a (m * n) → η (a : ℕ) = θ (a : ℕ) * χ (a : ℕ)) := by
    refine ⟨DirichletCharacter.mul θ χ, primitive_mul_of_coprime θ χ hθ hχ hc, ?_, ?_, ?_⟩
    · rw [MulChar.isQuadratic_iff_sq_eq_one, DirichletCharacter.mul, mul_pow]
      rw [← map_pow, ← map_pow, hqθ.sq_eq_one, hqχ.sq_eq_one, map_one, map_one, one_mul]
    · change (DirichletCharacter.mul θ χ) (-1) = -1
      rw [mul_eval_neg_one]
      exact hpar
    · intro a ha
      exact mul_eval_coprime_nat θ χ a (hc.lcm_eq_mul.symm ▸ ha)
  rw [hc.lcm_eq_mul] at h
  exact h

/-- Every complex character at an even level vanishes at two: a unit there would be
coprime to the level, contradicting evenness. This gives the dyadic value for characters
of conductor `4n` or `8n`. -/
private theorem even_level_character_two_zero {n : ℕ} (χ : DirichletCharacter ℂ n) (hn : Even n) :
    χ (2 : ℕ) = 0 := by
  apply χ.map_nonunit
  intro hu
  exact
    (Nat.not_odd_iff_even.mpr hn) (Nat.coprime_two_left.mp ((ZMod.isUnit_iff_coprime 2 n).mp hu))

/-- For `n ≡ 1 mod 4` and any odd natural number `p`, the product of `χ₄(p)` and
`J(p | n)` is `J(-4n | p)`. Apply quadratic reciprocity and the supplementary laws
at minus one and four. Primality and coprimality are not required; this supplies the
prime evaluation for the fourfold conductor branch. -/
private theorem four_discr_reciprocity (n p : ℕ) (hn : n % 4 = 1) (hp : Odd p) :
    ZMod.χ₄ (p : ℕ) * jacobiSym (p : ℤ) n = jacobiSym (-(4 * n : ℕ) : ℤ) p := by
  rw [Nat.cast_mul, Nat.cast_ofNat, jacobiSym.neg _ hp, jacobiSym.mul_left, jacobiSym.at_four hp,
    one_mul, jacobiSym.quadratic_reciprocity_one_mod_four' hp hn]

/-- For `n ≡ 1 mod 4` and odd `p`, the product `χ₈'(p) J(p | n)` is `J(-8n | p)`.
Write `χ₈'` as `χ₄χ₈` and apply quadratic reciprocity with the supplementary laws.
This supplies the negative-discriminant values in the even Jacobi-parity branch. -/
private theorem eight_discr_reciprocity_one (n p : ℕ) (hn : n % 4 = 1) (hp : Odd p) :
    ZMod.χ₈' (p : ℕ) * jacobiSym (p : ℤ) n = jacobiSym (-(8 * n : ℕ) : ℤ) p := by
  rw [ZMod.χ₈'_eq_χ₄_mul_χ₈]
  have hc : ZMod.χ₄ ((p : ZMod 8).cast : ZMod 4) = ZMod.χ₄ (p : ℕ) := by
    rw [ZMod.cast_natCast (show 4 ∣ 8 from by decide)]
  rw [hc, jacobiSym.quadratic_reciprocity_one_mod_four' hp hn]
  have h8 : jacobiSym 8 p = ZMod.χ₈ (p : ℕ) := by
    rw [show (8 : ℤ) = 4 * 2 from rfl, jacobiSym.mul_left, jacobiSym.at_four hp,
      jacobiSym.at_two hp, one_mul]
  rw [Nat.cast_mul, Nat.cast_ofNat, jacobiSym.neg _ hp, jacobiSym.mul_left, h8]
  ring

/-- For odd `n ≡ 3 mod 4` and odd `p`, `χ₈(p) J(p | n)` is `J(-8n | p)`.
Split the residue of `p` modulo four and apply quadratic reciprocity. This supplies
the negative-discriminant values in the odd Jacobi-parity branch. -/
private theorem eight_discr_reciprocity_three (n p : ℕ) (hn : n % 4 = 3) (hnOdd : Odd n)
    (hp : Odd p) : ZMod.χ₈ (p : ℕ) * jacobiSym (p : ℤ) n = jacobiSym (-(8 * n : ℕ) : ℤ) p := by
  have h8 : jacobiSym 8 p = ZMod.χ₈ (p : ℕ) := by
    rw [show (8 : ℤ) = 4 * 2 from rfl, jacobiSym.mul_left, jacobiSym.at_four hp,
      jacobiSym.at_two hp, one_mul]
  rw [Nat.cast_mul, Nat.cast_ofNat, jacobiSym.neg _ hp, jacobiSym.mul_left, h8]
  rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hp) with h1 | h3
  · rw [ZMod.χ₄_nat_one_mod_four h1, one_mul, jacobiSym.quadratic_reciprocity_one_mod_four h1 hnOdd]
  · rw [ZMod.χ₄_nat_three_mod_four h3, jacobiSym.quadratic_reciprocity_three_mod_four h3 hn]
    ring

/-- Extend a discriminant evaluation from coprime prime residues to all prime
residues. At a prime dividing the level, both the character and the Legendre symbol vanish. -/
private theorem prime_discr_value_of_coprime_value {q p : ℕ} (χ : DirichletCharacter ℂ q)
    [Fact p.Prime] (hv : Nat.Coprime p q → χ (p : ℕ) = (legendreSym p (-(q : ℤ)) : ℂ)) :
    χ (p : ℕ) = (legendreSym p (-(q : ℤ)) : ℂ) := by
  by_cases hc : Nat.Coprime p q
  · exact hv hc
  · have hd : p ∣ q := not_not.mp (((Fact.out : p.Prime).coprime_iff_not_dvd).mpr.mt hc)
    have hz : ((-(q : ℤ) : ℤ) : ZMod p) = 0 := by
      rw [Int.cast_neg, Int.cast_natCast, (ZMod.natCast_eq_zero_iff q p).mpr hd, neg_zero]
    have hv0 : χ (p : ℕ) = 0 := χ.map_nonunit (fun hu ↦ hc ((ZMod.isUnit_iff_coprime p q).mp hu))
    rw [hv0, (legendreSym.eq_zero_iff p (-(q : ℤ))).mpr hz, Int.cast_zero]

/-- For every natural `n`, `χ₈(-4n)` is zero. Check the eight possible residues of `n`
in the kernel and transport the integer casts. This matches the vanishing character
value at two in the even conductor branches. -/
private theorem chiEight_four_mul_zero (n : ℕ) : ZMod.χ₈ (-(4 * n : ℕ) : ℤ) = 0 := by
  have h := (by decide : ∀ x : ZMod 8, ZMod.χ₈ (-(4 * x)) = 0) (n : ZMod 8)
  simpa only [Nat.cast_mul, Nat.cast_ofNat, Int.cast_neg, Int.cast_mul, Int.cast_natCast,
    Int.cast_ofNat] using h

/-- For an odd squarefree conductor part one modulo four, construct a primitive odd
quadratic character at four times that level. Retain its negative discriminant values
at odd primes and its zero value at two. Reciprocity also covers primes dividing the level. -/
private theorem four_mul_odd_character_values (n : ℕ) (hn : Odd n) (hsq : Squarefree n)
    (hmod : n % 4 = 1) :
    ∃ χ : DirichletCharacter ℂ (4 * n),
      χ.IsPrimitive ∧
        χ.IsQuadratic ∧
        χ.Odd ∧
        (∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → χ (p : ℕ) = (legendreSym p (-(4 * n : ℕ) : ℤ) : ℂ)) ∧
        χ (2 : ℕ) = (ZMod.χ₈ (-(4 * n : ℕ) : ℤ) : ℂ) := by
  let : NeZero n := ⟨(Odd.pos hn).ne'⟩
  have hcop : Nat.Coprime 4 n := by
    have h := hn.coprime_two_left.pow_left 2
    norm_num only at h
    exact h
  have hpar :
    (ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)) (-1) * complexJacobiNumeratorCharacter n hn (-1) =
      -1 := by
    rw [chiFour_neg_one, jacobi_even_of_mod_four_one n hn hmod]
    ring
  obtain ⟨χ, hprim, hquad, hodd, hval⟩ :=
    primitive_odd_product_values (ZMod.χ₄.ringHomComp (Int.castRingHom ℂ))
      (complexJacobiNumeratorCharacter n hn) complexChiFour_isPrimitive
      (complexJacobiNumeratorCharacter_isPrimitive n hn hsq) (ZMod.isQuadratic_χ₄.comp _)
      (complexJacobiNumeratorCharacter_isQuadratic n hn) hcop hpar
  refine ⟨χ, hprim, hquad, hodd, ?_, ?_⟩
  · intro p hp hp2
    apply prime_discr_value_of_coprime_value χ
    intro hc
    rw [hval p hc]
    change (ZMod.χ₄ (p : ℕ) : ℂ) * complexJacobiNumeratorCharacter n hn (p : ℕ) = _
    have hj := complexJacobiNumeratorCharacter_apply_int n hn (p : ℤ)
    simp only [Int.cast_natCast] at hj
    rw [hj, ← Int.cast_mul]
    exact
      congrArg (fun z : ℤ ↦ (z : ℂ))
        ((four_discr_reciprocity n p hmod
              ((Fact.out : p.Prime).eq_two_or_odd'.resolve_left hp2)).trans
          (jacobiSym.legendreSym.to_jacobiSym p (-(4 * n : ℕ) : ℤ)).symm)
  · rw [even_level_character_two_zero χ
        (even_iff_two_dvd.mpr (dvd_mul_of_dvd_left (show 2 ∣ 4 from by decide) n)),
      chiEight_four_mul_zero n, Int.cast_zero]

/-- Choose the character modulo eight according to the odd conductor part modulo
four. Its parity product with the Jacobi numerator character is odd, and its values at
every odd natural number supply the negative-discriminant Jacobi symbols.
Use `χ₈'` for residue one and `χ₈` for residue three; reciprocity proves the evaluations.
This chooses the two-primary factor for conductor `8n`. -/
private theorem eight_primary_character_values (n : ℕ) (hn : Odd n) :
    ∃ θ : DirichletCharacter ℂ 8,
      θ.IsPrimitive ∧
        θ.IsQuadratic ∧
        θ (-1) * complexJacobiNumeratorCharacter n hn (-1) = -1 ∧
        (∀ p : ℕ,
          Odd p →
            θ (p : ℕ) * (jacobiSym (p : ℤ) n : ℂ) = (jacobiSym (-(8 * n : ℕ) : ℤ) p : ℂ)) := by
  rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hn) with h1 | h3
  · refine
      ⟨ZMod.χ₈'.ringHomComp (Int.castRingHom ℂ), complexChiEightPrime_isPrimitive,
        ZMod.isQuadratic_χ₈'.comp _, ?_, ?_⟩
    · rw [chiEightPrime_neg_one, jacobi_even_of_mod_four_one n hn h1]
      ring
    · intro p hp
      change (ZMod.χ₈' (p : ℕ) : ℂ) * (jacobiSym (p : ℤ) n : ℂ) = _
      rw [← Int.cast_mul]
      exact congrArg (fun z : ℤ ↦ (z : ℂ)) (eight_discr_reciprocity_one n p h1 hp)
  · refine
      ⟨ZMod.χ₈.ringHomComp (Int.castRingHom ℂ), complexChiEight_isPrimitive,
        ZMod.isQuadratic_χ₈.comp _, ?_, ?_⟩
    · rw [chiEight_neg_one, complexJacobiNumeratorCharacter_odd n hn h3]
      ring
    · intro p hp
      change (ZMod.χ₈ (p : ℕ) : ℂ) * (jacobiSym (p : ℤ) n : ℂ) = _
      rw [← Int.cast_mul]
      exact congrArg (fun z : ℤ ↦ (z : ℂ)) (eight_discr_reciprocity_three n p h3 hn hp)

/-- For an odd squarefree conductor part, combine its Jacobi numerator character
with the appropriate character modulo eight. The resulting primitive odd quadratic
character matches the negative discriminant at odd primes and vanishes at two. -/
private theorem eight_mul_odd_character_values (n : ℕ) (hn : Odd n) (hsq : Squarefree n) :
    ∃ χ : DirichletCharacter ℂ (8 * n),
      χ.IsPrimitive ∧
        χ.IsQuadratic ∧
        χ.Odd ∧
        (∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → χ (p : ℕ) = (legendreSym p (-(8 * n : ℕ) : ℤ) : ℂ)) ∧
        χ (2 : ℕ) = (ZMod.χ₈ (-(8 * n : ℕ) : ℤ) : ℂ) := by
  let : NeZero n := ⟨(Odd.pos hn).ne'⟩
  obtain ⟨θ, hprimθ, hquadθ, hpar, hrec⟩ := eight_primary_character_values n hn
  have hcop : Nat.Coprime 8 n := by
    have h := hn.coprime_two_left.pow_left 3
    norm_num only at h
    exact h
  obtain ⟨χ, hprim, hquad, hodd, hval⟩ :=
    primitive_odd_product_values θ (complexJacobiNumeratorCharacter n hn) hprimθ
      (complexJacobiNumeratorCharacter_isPrimitive n hn hsq) hquadθ
      (complexJacobiNumeratorCharacter_isQuadratic n hn) hcop hpar
  refine ⟨χ, hprim, hquad, hodd, ?_, ?_⟩
  · intro p hp hp2
    apply prime_discr_value_of_coprime_value χ
    intro hc
    rw [hval p hc]
    have hj := complexJacobiNumeratorCharacter_apply_int n hn (p : ℤ)
    simp only [Int.cast_natCast] at hj
    rw [hj, hrec p ((Fact.out : p.Prime).eq_two_or_odd'.resolve_left hp2), ←
      jacobiSym.legendreSym.to_jacobiSym]
  · have hz : ZMod.χ₈ (-(8 * n : ℕ) : ℤ) = 0 := by
      simpa only [show 4 * (2 * n) = 8 * n by ring] using chiEight_four_mul_zero (2 * n)
    rw [even_level_character_two_zero χ
        (even_iff_two_dvd.mpr (dvd_mul_of_dvd_left (show 2 ∣ 8 from by decide) n)),
      hz, Int.cast_zero]

/-- Every negative fundamental discriminant has a primitive odd quadratic character
whose values match its Legendre symbols at all odd primes and its character-modulo-eight
value at two. Construct the character together with these evaluations in the odd,
fourfold, and eightfold conductor branches. This supplies one matching character
for all local quadratic splitting formulas, including ramified and dyadic primes. -/
theorem exists_primitive_character_values_of_fundamental_discr (q : ℕ)
    (hf : Int.IsFundamentalDiscr (-(q : ℤ))) :
    ∃ χ : DirichletCharacter ℂ q,
      χ.IsPrimitive ∧
        χ.IsQuadratic ∧
        χ.Odd ∧
        (∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → χ (p : ℕ) = (legendreSym p (-(q : ℤ)) : ℂ)) ∧
        χ (2 : ℕ) = (ZMod.χ₈ (-(q : ℤ)) : ℂ) := by
  rcases Int.isFundamentalDiscr_iff_squarefree.mp hf with ⟨hm, _hs⟩ | ⟨hm, hs, hr⟩
  · have hqodd := odd_of_mod_four_three q (negative_mod_four_one q hm)
    exact exists_primitive_character_values_of_negative_odd_fundamental q hqodd hf
  · have hdZ : (4 : ℤ) ∣ (q : ℤ) := dvd_neg.mp (Int.dvd_iff_emod_eq_zero.mpr hm)
    have hd : 4 ∣ q := by exact_mod_cast hdZ
    obtain ⟨n, rfl⟩ := hd
    have hquot : (-(4 * n : ℕ) : ℤ) / 4 = -(n : ℤ) := by
      simp only [Nat.cast_mul, Nat.cast_ofNat]
      rw [← Int.mul_neg, Int.mul_ediv_cancel_left _ (show (4 : ℤ) ≠ 0 from by norm_num only)]
    rw [hquot] at hs hr
    have hsq : Squarefree n := by
      have h := Int.squarefree_natAbs.mpr hs
      simpa only [Int.natAbs_neg, Int.natAbs_natCast] using h
    rcases negative_mod_four_two_or_three n hr with h2 | h1
    · have hn2 : n % 2 = 0 := by rw [← Nat.mod_mod_of_dvd n (show 2 ∣ 4 from by norm_num only), h2]
      have hdiv : 2 ∣ n := even_iff_two_dvd.mp (Nat.even_iff.mpr hn2)
      obtain ⟨m, rfl⟩ := hdiv
      have hmOdd : Odd m := by
        apply Nat.odd_iff.mpr
        have hh : 2 * (m % 2) = 2 := by
          simpa only [show (4 : ℕ) = 2 * 2 from rfl, Nat.mul_mod_mul_left] using h2
        exact Nat.eq_of_mul_eq_mul_left (show 0 < (2 : ℕ) from by norm_num only) hh
      have hmSq : Squarefree m := hsq.squarefree_of_dvd (Nat.dvd_mul_left m 2)
      rw [show 4 * (2 * m) = 8 * m by ring]
      simpa only [Int.cast_neg] using eight_mul_odd_character_values m hmOdd hmSq
    · simpa only [Int.cast_neg] using
        four_mul_odd_character_values n (odd_of_mod_four_one n h1) hsq h1

end PseudoPrime.NumberTheory
