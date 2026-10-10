/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind
public import Mathlib.NumberTheory.NumberField.Ideal.Basic
public import Mathlib.RingTheory.RamificationInertia.Ramification

/-!
# Rational prime ideal factorization in number fields

Express `(p)` as the product of primes above `p` with ramification-index exponents.
When `p` does not divide an integral generator's exponent, Kummer-Dedekind replaces
these primes and exponents by reduced polynomial factors and their multiplicities.
Their degrees also determine the absolute norms, providing the data for local ideal counts.
-/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- For an integral generator whose exponent is prime to `p`, the prime ideal corresponding
to a monic factor of its reduced minimal polynomial has absolute norm `p` raised to the
factor degree. Kummer-Dedekind identifies the inertia degree, and the residue-field norm
formula converts it to an absolute norm. This supplies the norm condition in local ideal
counting for ramified, inert, and split primes. -/
theorem absNorm_primeIdeal_of_monicFactor (K : Type) [Field K] [NumberField K]
    (θ : NumberField.RingOfIntegers K) (p : ℕ) [Fact p.Prime] (hp : ¬p ∣ RingOfIntegers.exponent θ)
    (Q : RingOfIntegers.monicFactorsMod θ p) :
    Ideal.absNorm
        ((NumberField.Ideal.primesOverSpanEquivMonicFactorsMod hp).symm Q :
          Ideal (NumberField.RingOfIntegers K)) =
      p ^ Q.val.natDegree := by
  let P := (NumberField.Ideal.primesOverSpanEquivMonicFactorsMod hp).symm Q
  let : (P : Ideal (NumberField.RingOfIntegers K)).IsPrime := P.property.1
  let : (P : Ideal (NumberField.RingOfIntegers K)).LiesOver (Ideal.span {(p : ℤ)}) := P.property.2
  exact
    (Ideal.pow_inertiaDeg p (P : Ideal (NumberField.RingOfIntegers K))).symm.trans
      (congrArg (p ^ ·)
        (NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply' hp Q.property))

/-- In a number field, the principal ideal of a rational prime is the product of the
prime ideals above it, each raised to its ramification index. Dedekind factorization
expresses the ideal as a product of normalized factors; the ramification index counts
each factor. This turns local ramification data into the ideal equalities used in counting. -/
theorem principal_prime_eq_prod_ramification (K : Type) [Field K] [NumberField K] (p : ℕ)
    [Fact p.Prime] :
    Ideal.span {(p : NumberField.RingOfIntegers K)} =
      ∏ Q : (Ideal.span {(p : ℤ)}).primesOver (NumberField.RingOfIntegers K),
        (Q : Ideal (NumberField.RingOfIntegers K)) ^
          (Q : Ideal (NumberField.RingOfIntegers K)).ramificationIdx ℤ := by
  classical
  let : (Ideal.span {(p : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p
  have hp0 : Ideal.span {(p : ℤ)} ≠ ⊥ :=
    mt Ideal.span_singleton_eq_bot.mp (Int.natCast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  let J := (Ideal.span {(p : ℤ)}).map (algebraMap ℤ (NumberField.RingOfIntegers K))
  have hj0 : J ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot hp0
  have hj : J = Ideal.span {(p : NumberField.RingOfIntegers K)} := by
    simp only [J, Ideal.map_span, Set.image_singleton, map_natCast]
  rw [← hj, ← normalize_eq J, ← UniqueFactorizationMonoid.prod_normalizedFactors_eq hj0,
    Finset.prod_multiset_count]
  rw [Finset.prod_subtype _
      (fun Q =>
        (Multiset.mem_toFinset.trans
          (Ideal.mem_primesOver_iff_mem_normalizedFactors (NumberField.RingOfIntegers K)
              hp0).symm))]
  apply Finset.prod_congr rfl
  intro Q _
  let : (Q : Ideal (NumberField.RingOfIntegers K)).LiesOver (Ideal.span {(p : ℤ)}) := Q.property.2
  exact
    congrArg ((Q : Ideal (NumberField.RingOfIntegers K)) ^ ·)
      (Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count (Ideal.span {(p : ℤ)})
          (Q : Ideal (NumberField.RingOfIntegers K)) hj0).symm

/-- If a rational prime does not divide the exponent of an integral generator, its
principal ideal is the product of the prime ideals corresponding to the monic factors
of the reduced minimal polynomial, with exponents given by factor multiplicities.
Transport the prime-ideal product through Kummer-Dedekind. This provides the actual
ideal factorization needed to apply the ramified, inert, and split counting formulas. -/
theorem principal_prime_eq_prod_monicFactors (K : Type) [Field K] [NumberField K]
    (θ : NumberField.RingOfIntegers K) (p : ℕ) [Fact p.Prime]
    (hp : ¬p ∣ RingOfIntegers.exponent θ) :
    Ideal.span {(p : NumberField.RingOfIntegers K)} =
      ∏ Q : RingOfIntegers.monicFactorsMod θ p,
        ((NumberField.Ideal.primesOverSpanEquivMonicFactorsMod hp).symm Q :
            Ideal (NumberField.RingOfIntegers K)) ^
          multiplicity Q.val ((minpoly ℤ θ).map (Int.castRingHom (ZMod p))) := by
  classical
  rw [principal_prime_eq_prod_ramification K p]
  let e := NumberField.Ideal.primesOverSpanEquivMonicFactorsMod hp
  apply
    (e.symm.prod_comp
        (fun P =>
          (P : Ideal (NumberField.RingOfIntegers K)) ^
            (P : Ideal (NumberField.RingOfIntegers K)).ramificationIdx ℤ)).symm.trans
  apply Finset.prod_congr rfl
  intro Q _
  exact
    congrArg
      (((NumberField.Ideal.primesOverSpanEquivMonicFactorsMod hp).symm Q :
          Ideal (NumberField.RingOfIntegers K)) ^
        ·)
      (NumberField.Ideal.ramificationIdx_primesOverSpanEquivMonicFactorsMod_symm_apply' hp
        Q.property)

/-- If the reduced minimal polynomial of an integral generator is irreducible and its
exponent is prime to `p`, the principal ideal `(p)` is prime. Its quotient is isomorphic
to the polynomial quotient, which is a domain. This supplies the inert ideal in the
local splitting classification. -/
theorem principal_prime_isPrime_of_irreducible_minpoly_mod (K : Type) [Field K] [NumberField K]
    (θ : NumberField.RingOfIntegers K) (p : ℕ) [Fact p.Prime] (hp : ¬p ∣ RingOfIntegers.exponent θ)
    (hi : Irreducible ((minpoly ℤ θ).map (Int.castRingHom (ZMod p)))) :
    (Ideal.span {(p : NumberField.RingOfIntegers K)}).IsPrime := by
  let : (Ideal.span {((minpoly ℤ θ).map (Int.castRingHom (ZMod p)))}).IsPrime :=
    (Ideal.span_singleton_prime hi.ne_zero).mpr hi.prime
  let e := RingOfIntegers.ZModXQuotSpanEquivQuotSpan hp
  let :
    IsDomain
      ((Polynomial (ZMod p)) ⧸ Ideal.span {((minpoly ℤ θ).map (Int.castRingHom (ZMod p)))}) :=
    (Ideal.Quotient.isDomain_iff_prime _).mpr inferInstance
  exact
    (Ideal.Quotient.isDomain_iff_prime _).mp (Function.Injective.isDomain e.symm e.symm.injective)

end PseudoPrime.NumberTheory
