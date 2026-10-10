/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.QuadraticPolynomial
public import PseudoPrime.NumberTheory.QuadraticPrimeSplitting
public import PseudoPrime.NumberTheory.QuadraticDiscriminantCharacter
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.NumberTheory.LegendreSymbol.ZModChar

/-!
# Prime splitting from quadratic discriminant values

Classify the reduced polynomial of an integral quadratic generator and apply
Kummer-Dedekind to obtain the actual prime-ideal splitting and absolute norms.
-/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- For an odd rational prime, a character whose value is the Legendre symbol of
the discriminant agrees with the prime splitting of the quadratic number field.
The integral generator has minimal polynomial `X^2 - b*X - a`, and the prime does
not divide its exponent. Classify the reduced discriminant as zero, nonsquare, or
nonzero square and apply the corresponding ideal factorization. This supplies the
local arithmetic condition needed for the quadratic Dedekind coefficient identity. -/
theorem quadraticPrimeSplittingAt_of_odd_prime_discr (K : Type) [Field K] [NumberField K]
    (hdeg : Module.finrank ℚ K = 2) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (θ : NumberField.RingOfIntegers K) (a b D : ℤ)
    (hf : minpoly ℤ θ = Polynomial.X ^ 2 - Polynomial.C b * Polynomial.X - Polynomial.C a)
    (hd : D = b ^ 2 + 4 * a) (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (hp : ¬p ∣ RingOfIntegers.exponent θ) (hc : χ (p : ℕ) = (legendreSym p D : ℂ)) :
    quadraticPrimeSplittingAt K χ p := by
  have hpnot : ¬p ∣ 2 := fun h ↦
    hp2 (((Nat.dvd_prime Nat.prime_two).mp h).resolve_left (Fact.out : p.Prime).ne_one)
  let : NeZero (2 : ZMod p) := ⟨fun h ↦ hpnot ((ZMod.natCast_eq_zero_iff 2 p).mp h)⟩
  have hF :
    (minpoly ℤ θ).map (Int.castRingHom (ZMod p)) =
      Polynomial.X ^ 2 - Polynomial.C (b : ZMod p) * Polynomial.X - Polynomial.C (a : ZMod p) := by
    rw [hf]
    simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_mul, Polynomial.map_X,
      Polynomial.map_C]
    rfl
  have hD : (D : ZMod p) = (b : ZMod p) ^ 2 + 4 * (a : ZMod p) := by
    rw [hd]
    simp only [Int.cast_add, Int.cast_pow, Int.cast_mul, Int.cast_ofNat]
  by_cases hz : (D : ZMod p) = 0
  · obtain ⟨r, hr⟩ :=
      quadratic_factorization_of_discr_zero (a : ZMod p) (b : ZMod p) (hD.symm.trans hz)
    apply quadraticPrimeSplittingAt_of_reduced_square K χ θ p hp r (hF.trans hr)
    rw [hc, (legendreSym.eq_zero_iff p D).mpr hz, Int.cast_zero]
  · by_cases hs : IsSquare (D : ZMod p)
    · obtain ⟨r, s, hrs, hr⟩ :=
        quadratic_factorization_of_nonzero_square_discr (a : ZMod p) (b : ZMod p) (hD.symm ▸ hz)
          (hD ▸ hs)
      apply
        quadraticPrimeSplittingAt_of_reduced_distinct_linear_factors K χ θ p hp r s hrs
          (hF.trans hr)
      rw [hc, (legendreSym.eq_one_iff p hz).mpr hs, Int.cast_one]
    · apply quadraticPrimeSplittingAt_of_irreducible K hdeg χ θ p hp
      · rw [hF]
        exact quadratic_irreducible_of_nonsquare (a : ZMod p) (b : ZMod p) (hD ▸ hs)
      · rw [hc, (legendreSym.eq_neg_one_iff p).mpr hs, Int.cast_neg, Int.cast_one]

/-- Every element of `ZMod 2` is zero or one. Bound its natural representative by one
and transfer the two possibilities back to the residue field. This gives the four
coefficient cases in the dyadic quadratic splitting proof. -/
private theorem zmodTwo_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.lt_succ_iff.mp (ZMod.val_lt x)) with h | h
  · exact Or.inl ((ZMod.val_eq_zero x).mp h)
  · exact Or.inr ((ZMod.val_eq_one (by decide) x).mp h)

/-- In a degree-two number field, the coefficients of a reduced monic quadratic
classify splitting at two, provided two does not divide the generator's exponent.
A zero middle coefficient gives a repeated root. With middle coefficient one,
a zero constant coefficient gives two roots, and constant coefficient one gives
an irreducible polynomial. Matching these coefficient values with the character
value yields the actual prime ideals, their norms, and the factorization of `(2)`.
This supplies the dyadic case of the quadratic Dedekind coefficient identity. -/
theorem quadraticPrimeSplittingAt_at_two (K : Type) [Field K] [NumberField K]
    (hdeg : Module.finrank ℚ K = 2) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (θ : NumberField.RingOfIntegers K) (a b : ZMod 2)
    (hf :
      (minpoly ℤ θ).map (Int.castRingHom (ZMod 2)) =
        Polynomial.X ^ 2 - Polynomial.C b * Polynomial.X - Polynomial.C a)
    (hp : ¬2 ∣ RingOfIntegers.exponent θ)
    (hc : χ (2 : ℕ) = if b = 0 then 0 else if a = 0 then 1 else -1) :
    quadraticPrimeSplittingAt K χ 2 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnd : (Polynomial.X ^ 2 - Polynomial.C b * Polynomial.X - Polynomial.C a).natDegree = 2 := by
    simpa only [map_neg, sub_eq_add_neg] using
      (Polynomial.isMonicOfDegree_sub_add_two b (-a)).natDegree_eq
  rcases zmodTwo_eq_zero_or_one a with rfl | rfl <;> rcases zmodTwo_eq_zero_or_one b with rfl | rfl
  · apply quadraticPrimeSplittingAt_of_reduced_square K χ θ 2 hp 0
    · rw [hf]
      simp only [Polynomial.C_0, zero_mul, sub_zero]
    · simpa only [ite_true] using hc
  · apply quadraticPrimeSplittingAt_of_reduced_distinct_linear_factors K χ θ 2 hp 0 1 zero_ne_one
    · rw [hf]
      simp only [Polynomial.C_0, Polynomial.C_1, one_mul, sub_zero]
      ring
    · simpa only [one_ne_zero, ite_false, ite_true] using hc
  · apply quadraticPrimeSplittingAt_of_reduced_square K χ θ 2 hp 1
    · rw [hf]
      simp only [Polynomial.C_0, Polynomial.C_1, zero_mul, sub_zero]
      simp only [sub_eq_add_neg, CharTwo.neg_eq, add_sq, CharTwo.two_eq_zero, zero_mul, add_zero,
        one_pow]
    · simpa only [ite_true] using hc
  · apply quadraticPrimeSplittingAt_of_irreducible K hdeg χ θ 2 hp
    · rw [hf]
      apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
      · rw [hnd]
        exact Finset.mem_Icc.mpr ⟨by decide, by decide⟩
      · intro x hx
        simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_mul,
          Polynomial.eval_X, Polynomial.eval_C] at hx
        rcases zmodTwo_eq_zero_or_one x with rfl | rfl
        · exact (by decide : (0 : ZMod 2) ^ 2 - 1 * 0 - 1 ≠ 0) hx
        · exact (by decide : (1 : ZMod 2) ^ 2 - 1 * 1 - 1 ≠ 0) hx
    · simpa only [one_ne_zero, ite_false] using hc

/-- The character modulo eight detects the two coefficient residues of a monic quadratic.
Check the 64 residue pairs in the kernel; its value is zero for an even middle
coefficient, and otherwise distinguishes split and inert reduction modulo two. -/
private theorem chiEight_quadratic_coefficients (a b : ZMod 8) :
    ZMod.χ₈ (b ^ 2 + 4 * a) =
      if ZMod.castHom (show 2 ∣ 8 from by decide) (ZMod 2) b = 0 then 0
      else if ZMod.castHom (show 2 ∣ 8 from by decide) (ZMod 2) a = 0 then 1 else -1 := by
  exact
    (by decide :
        ∀ a b : ZMod 8,
          ZMod.χ₈ (b ^ 2 + 4 * a) =
            if ZMod.castHom (show 2 ∣ 8 from by decide) (ZMod 2) b = 0 then 0
            else if ZMod.castHom (show 2 ∣ 8 from by decide) (ZMod 2) a = 0 then 1 else -1)
      a b

/-- For a degree-two number field with generator polynomial `X² - bX - a`, suppose
two does not divide the generator's exponent and `χ(2) = χ₈(b² + 4a)`.
Then quadratic prime splitting agrees with `χ` at two. Reduce the integral generator
polynomial and use the finite coefficient classification. This handles the dyadic prime
in the same splitting condition as the odd primes. -/
theorem quadraticPrimeSplittingAt_of_two_discr (K : Type) [Field K] [NumberField K]
    (hdeg : Module.finrank ℚ K = 2) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (θ : NumberField.RingOfIntegers K) (a b D : ℤ)
    (hf : minpoly ℤ θ = Polynomial.X ^ 2 - Polynomial.C b * Polynomial.X - Polynomial.C a)
    (hd : D = b ^ 2 + 4 * a) (hp : ¬2 ∣ RingOfIntegers.exponent θ)
    (hc : χ (2 : ℕ) = (ZMod.χ₈ (D : ZMod 8) : ℂ)) : quadraticPrimeSplittingAt K χ 2 := by
  have hF :
    (minpoly ℤ θ).map (Int.castRingHom (ZMod 2)) =
      Polynomial.X ^ 2 - Polynomial.C (b : ZMod 2) * Polynomial.X - Polynomial.C (a : ZMod 2) := by
    rw [hf]
    simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_mul, Polynomial.map_X,
      Polynomial.map_C]
    rfl
  apply quadraticPrimeSplittingAt_at_two K hdeg χ θ (a : ZMod 2) (b : ZMod 2) hF hp
  rw [hc, hd]
  have h :=
    congrArg (fun z : ℤ ↦ (z : ℂ)) (chiEight_quadratic_coefficients (a : ZMod 8) (b : ZMod 8))
  simpa only [Int.cast_add, Int.cast_pow, Int.cast_mul, Int.cast_ofNat, map_intCast, Int.cast_ite,
    Int.cast_zero, Int.cast_one, Int.cast_neg] using h

/-- A degree-two number field of negative discriminant `-q` has a primitive odd
quadratic character whose values describe the splitting of every rational prime.
Construct the character together with its discriminant evaluations, choose the
integral generator of exponent one, and classify its reduced polynomial at each
prime. This proves the arithmetic input to quadratic Dedekind factorization without
assuming ideal counts or a separate splitting correspondence. -/
theorem exists_primitive_character_splitting_of_discr (q : ℕ) (K : Type) [Field K] [NumberField K]
    (hdeg : Module.finrank ℚ K = 2) (hd : NumberField.discr K = -(q : ℤ)) :
    ∃ χ : DirichletCharacter ℂ q,
      χ.IsPrimitive ∧
        χ.IsQuadratic ∧ χ.Odd ∧ ∀ p : ℕ, p.Prime → quadraticPrimeSplittingAt K χ p := by
  have hf : Int.IsFundamentalDiscr (-(q : ℤ)) := hd ▸ quadratic_discr_isFundamental K hdeg
  obtain ⟨χ, hprim, hquad, hodd, hvals, htwo⟩ :=
    exists_primitive_character_values_of_fundamental_discr q hf
  obtain ⟨a, b, θ, had, hpoly, hdiscr⟩ := quadratic_exists_integral_generator_polynomial K hdeg
  have hexp : RingOfIntegers.exponent θ = 1 := RingOfIntegers.exponent_eq_one_iff.mpr had
  refine ⟨χ, hprim, hquad, hodd, ?_⟩
  intro p hp
  let : Fact p.Prime := ⟨hp⟩
  have hnot : ¬p ∣ RingOfIntegers.exponent θ := hexp.symm ▸ hp.not_dvd_one
  by_cases hp2 : p = 2
  · subst p
    apply
      quadraticPrimeSplittingAt_of_two_discr K hdeg χ θ a b (-(q : ℤ)) hpoly (hd.symm.trans hdiscr)
        hnot
    simpa only [Int.cast_neg] using htwo
  · exact
      quadraticPrimeSplittingAt_of_odd_prime_discr K hdeg χ θ a b (-(q : ℤ)) hpoly
        (hd.symm.trans hdiscr) p hp2 hnot (hvals p hp2)

end PseudoPrime.NumberTheory
