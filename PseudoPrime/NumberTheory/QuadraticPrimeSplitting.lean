/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.QuadraticFieldArithmetic
public import PseudoPrime.NumberTheory.PrimePowerIdealNormCount
public import PseudoPrime.NumberTheory.PrimeIdealFactorization

/-!
# Prime splitting interfaces for quadratic number fields

Use integral quadratic generators of index one to apply Kummer-Dedekind at every prime,
with the residual degrees and ramification indices identified by polynomial factorization.
-/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- The canonical basis `1, ω` of the integral quadratic algebra is a power basis.
Its generator is `ω`, its dimension is two, and its two basis vectors are powers
with exponents zero and one. This computes the exact minimal polynomial of the model. -/
private noncomputable def model_powerBasis (a b : ℤ) : PowerBasis ℤ (QuadraticAlgebra ℤ a b) where
  gen := QuadraticAlgebra.omega
  dim := 2
  basis := QuadraticAlgebra.basis a b
  basis_eq_pow := by
    intro i
    fin_cases i
    · exact (QuadraticAlgebra.basis_apply_zero a b).trans (pow_zero _).symm
    · exact QuadraticAlgebra.basis_apply_one.trans (pow_one _).symm

/-- In the integral model with `ω² = a + bω`, the minimal polynomial of `ω`
is `X² - bX - a`. Compute the power-basis polynomial from the two coordinates
of `ω²`. This identifies the polynomial to be reduced in Kummer-Dedekind. -/
private theorem model_minpoly (a b : ℤ) :
    minpoly ℤ (QuadraticAlgebra.omega : QuadraticAlgebra ℤ a b) =
      Polynomial.X ^ 2 - Polynomial.C b * Polynomial.X - Polynomial.C a := by
  have h := (model_powerBasis a b).minpolyGen_eq
  change
    (model_powerBasis a b).minpolyGen =
      minpoly ℤ (QuadraticAlgebra.omega : QuadraticAlgebra ℤ a b) at h
  rw [← h]
  unfold PowerBasis.minpolyGen
  change
    Polynomial.X ^ 2 -
        (∑ i : Fin 2,
          Polynomial.C
              ((QuadraticAlgebra.basis a b).repr
                ((QuadraticAlgebra.omega : QuadraticAlgebra ℤ a b) ^ 2) i) *
            Polynomial.X ^ (i : ℕ)) =
      _
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, mul_one, sq,
    QuadraticAlgebra.omega_mul_omega_eq_mk, QuadraticAlgebra.basis_repr_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  ring

/-- The generator in an integral quadratic model generates the whole ring of integers.
Transport the canonical quadratic algebra generation identity along the algebra equivalence.
This ensures that no rational prime is excluded from Kummer-Dedekind by an order index. -/
private theorem model_generator_adjoin (K : Type) [Field K] [NumberField K] (a b : ℤ)
    (f : NumberField.RingOfIntegers K ≃ₐ[ℤ] QuadraticAlgebra ℤ a b) :
    Algebra.adjoin ℤ {f.symm QuadraticAlgebra.omega} = ⊤ := by
  have h := f.symm.toAlgHom.map_adjoin_singleton QuadraticAlgebra.omega
  rw [QuadraticAlgebra.adjoin_omega_eq_top, Algebra.map_top] at h
  exact h.symm.trans ((AlgHom.range_eq_top _).mpr f.symm.surjective)

/-- Every degree-two number field has a generator of its entire ring of integers
with minimal polynomial `X² - bX - a` and field discriminant `b² + 4a`.
Transport the canonical quadratic generator and its minimal polynomial along the
integral algebra equivalence. The exact coefficients connect prime splitting of the
field with the discriminant of the reduced quadratic polynomial. -/
theorem quadratic_exists_integral_generator_polynomial (K : Type) [Field K] [NumberField K]
    (hdeg : Module.finrank ℚ K = 2) :
    ∃ a b : ℤ,
      ∃ θ : NumberField.RingOfIntegers K,
        Algebra.adjoin ℤ {θ} = ⊤ ∧
          minpoly ℤ θ = Polynomial.X ^ 2 - Polynomial.C b * Polynomial.X - Polynomial.C a ∧
          NumberField.discr K = b ^ 2 + 4 * a := by
  obtain ⟨a, b, f, hd⟩ := quadratic_ringOfIntegers_model K hdeg
  refine ⟨a, b, f.symm QuadraticAlgebra.omega, ?_, ?_, hd⟩
  · exact model_generator_adjoin K a b f
  · exact (minpoly.algEquiv_eq f.symm QuadraticAlgebra.omega).trans (model_minpoly a b)

/-- Every degree-two number field has an integral generator with Kummer-Dedekind exponent one.
Choose the generator from the integral quadratic algebra model. It generates the entire
ring of integers, so its Kummer-Dedekind exponent is one by the adjoin characterization.
This provides a single generator suitable for splitting every rational prime. -/
theorem quadratic_exists_integral_generator (K : Type) [Field K] [NumberField K]
    (hdeg : Module.finrank ℚ K = 2) :
    ∃ θ : NumberField.RingOfIntegers K,
      Algebra.adjoin ℤ {θ} = ⊤ ∧ RingOfIntegers.exponent θ = 1 := by
  obtain ⟨_a, _b, θ, had, _hpoly, _hd⟩ := quadratic_exists_integral_generator_polynomial K hdeg
  exact ⟨θ, had, RingOfIntegers.exponent_eq_one_iff.mpr had⟩

/-- In a degree-two number field, choose one integral generator such that, for every prime,
the prime ideals above that prime correspond to the monic irreducible factors of its
reduced minimal polynomial. The residual degree is the polynomial factor degree and
the ramification index is its multiplicity. The absolute norm is the prime raised
to the factor degree. The integral generator has exponent one,
so Kummer-Dedekind applies at every prime, including ramified primes.
This supplies the local factorization interface for the ideal counting formula. -/
theorem quadratic_exists_prime_factor_equiv (K : Type) [Field K] [NumberField K]
    (hdeg : Module.finrank ℚ K = 2) :
    ∃ θ : NumberField.RingOfIntegers K,
      Algebra.adjoin ℤ {θ} = ⊤ ∧
        ∀ (p : ℕ) [Fact p.Prime],
          ∃ e :
            (Ideal.span {(p : ℤ)}).primesOver (NumberField.RingOfIntegers K) ≃
              RingOfIntegers.monicFactorsMod θ p,
            ∀ Q,
              (e.symm Q : Ideal (NumberField.RingOfIntegers K)).inertiaDeg ℤ = Q.val.natDegree ∧
                (e.symm Q : Ideal (NumberField.RingOfIntegers K)).ramificationIdx ℤ =
                  multiplicity Q.val ((minpoly ℤ θ).map (Int.castRingHom (ZMod p))) ∧
                Ideal.absNorm (e.symm Q : Ideal (NumberField.RingOfIntegers K)) =
                  p ^ Q.val.natDegree := by
  obtain ⟨θ, had, hexp⟩ := quadratic_exists_integral_generator K hdeg
  refine ⟨θ, had, ?_⟩
  intro p hp
  have hnot : ¬p ∣ RingOfIntegers.exponent θ := by
    rw [hexp]
    exact (Fact.out : p.Prime).not_dvd_one
  refine ⟨NumberField.Ideal.primesOverSpanEquivMonicFactorsMod hnot, ?_⟩
  intro Q
  exact
    ⟨NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply' hnot Q.property,
      NumberField.Ideal.ramificationIdx_primesOverSpanEquivMonicFactorsMod_symm_apply' hnot
        Q.property,
      absNorm_primeIdeal_of_monicFactor K θ p hnot Q⟩

/-- In a degree-two number field, an irreducible reduced minimal polynomial and
character value `-1` give the inert case, provided `p` does not divide the generator's
Kummer-Dedekind exponent. The principal ideal is prime by the quotient presentation,
and its norm is `p^2` by the degree of the number field. This connects polynomial
irreducibility to prime-power ideal counts. -/
theorem quadraticPrimeSplittingAt_of_irreducible (K : Type) [Field K] [NumberField K]
    (hdeg : Module.finrank ℚ K = 2) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (θ : NumberField.RingOfIntegers K) (p : ℕ) [Fact p.Prime] (hp : ¬p ∣ RingOfIntegers.exponent θ)
    (hi : Irreducible ((minpoly ℤ θ).map (Int.castRingHom (ZMod p)))) (hc : χ (p : ℕ) = -1) :
    quadraticPrimeSplittingAt K χ p := by
  have hn : (p : NumberField.RingOfIntegers K) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  refine Or.inr (Or.inl ⟨hc, Ideal.span {(p : NumberField.RingOfIntegers K)}, ?_, rfl, ?_⟩)
  · exact
      Ideal.prime_of_isPrime (mt Ideal.span_singleton_eq_bot.mp hn)
        (principal_prime_isPrime_of_irreducible_minpoly_mod K θ p hp hi)
  · exact
      (Ideal.absNorm_span_natCast p).trans
        (congrArg (p ^ ·) ((NumberField.RingOfIntegers.rank K).trans hdeg))

/-- Over a field, the normalized factors of `(X - r)²` are two copies of `X - r`.
The linear factor is irreducible and monic, so normalization fixes it. This identifies
the unique factor in the ramified Kummer-Dedekind product. -/
private theorem linear_square_factors {F : Type} [Field F] [DecidableEq F] (r : F) :
    UniqueFactorizationMonoid.normalizedFactors ((Polynomial.X - Polynomial.C r) ^ 2) =
      Multiset.replicate 2 (Polynomial.X - Polynomial.C r) := by
  rw [(Polynomial.irreducible_X_sub_C r).normalizedFactors_pow,
    (Polynomial.monic_X_sub_C r).normalize_eq_self]

/-- Over a field, `X - r` has multiplicity two in `(X - r)²`.
Count its copies in the normalized factor multiset. This gives ramification index two
for a squared linear reduction. -/
private theorem linear_square_multiplicity {F : Type} [Field F] (r : F) :
    multiplicity (Polynomial.X - Polynomial.C r) ((Polynomial.X - Polynomial.C r) ^ 2) = 2 := by
  classical
  rw [UniqueFactorizationMonoid.multiplicity_eq_count_normalizedFactors
      (Polynomial.irreducible_X_sub_C r) (pow_ne_zero 2 (Polynomial.X_sub_C_ne_zero r)),
    (Polynomial.monic_X_sub_C r).normalize_eq_self, linear_square_factors]
  exact Multiset.count_replicate_self _ 2

/-- Over a field, the normalized factors of `(X - r)(X - s)` are `X - r` and `X - s`,
with repetition allowed. Multiply the factor multisets and use monicity to normalize.
This identifies the factors in the split Kummer-Dedekind product. -/
private theorem linear_product_factors {F : Type} [Field F] [DecidableEq F] (r s : F) :
    UniqueFactorizationMonoid.normalizedFactors
        ((Polynomial.X - Polynomial.C r) * (Polynomial.X - Polynomial.C s)) =
      {Polynomial.X - Polynomial.C r} + {Polynomial.X - Polynomial.C s} := by
  rw [UniqueFactorizationMonoid.normalizedFactors_mul (Polynomial.X_sub_C_ne_zero r)
      (Polynomial.X_sub_C_ne_zero s),
    UniqueFactorizationMonoid.normalizedFactors_irreducible (Polynomial.irreducible_X_sub_C r),
    UniqueFactorizationMonoid.normalizedFactors_irreducible (Polynomial.irreducible_X_sub_C s),
    (Polynomial.monic_X_sub_C r).normalize_eq_self, (Polynomial.monic_X_sub_C s).normalize_eq_self]

/-- For distinct field elements `r` and `s`, `X - r` occurs once in `(X - r)(X - s)`.
Count normalized factors and use injectivity of the constant-polynomial map to separate
them. This gives ramification index one in the split case. -/
private theorem linear_product_multiplicity {F : Type} [Field F] (r s : F) (hrs : r ≠ s) :
    multiplicity (Polynomial.X - Polynomial.C r)
        ((Polynomial.X - Polynomial.C r) * (Polynomial.X - Polynomial.C s)) =
      1 := by
  classical
  have hlin : Polynomial.X - Polynomial.C r ≠ Polynomial.X - Polynomial.C s := fun h ↦
    hrs (Polynomial.C_injective (sub_right_inj.mp h))
  rw [UniqueFactorizationMonoid.multiplicity_eq_count_normalizedFactors
      (Polynomial.irreducible_X_sub_C r)
      (mul_ne_zero (Polynomial.X_sub_C_ne_zero r) (Polynomial.X_sub_C_ne_zero s)),
    (Polynomial.monic_X_sub_C r).normalize_eq_self, linear_product_factors]
  simp only [Multiset.count_add, Multiset.count_singleton, ite_true, ite_false, hlin, add_zero]

/-- If the reduced minimal polynomial is a squared linear factor and the character
vanishes at `p`, with `p` not dividing the generator's exponent, the prime is ramified:
its principal ideal is the square of a prime ideal of norm `p`.
Factor multiplicity two gives the ideal square and factor degree one gives the norm.
This supplies the ramified input to ideal counting. -/
theorem quadraticPrimeSplittingAt_of_reduced_square (K : Type) [Field K] [NumberField K] {q : ℕ}
    (χ : DirichletCharacter ℂ q) (θ : NumberField.RingOfIntegers K) (p : ℕ) [Fact p.Prime]
    (hp : ¬p ∣ RingOfIntegers.exponent θ) (r : ZMod p)
    (hf : (minpoly ℤ θ).map (Int.castRingHom (ZMod p)) = (Polynomial.X - Polynomial.C r) ^ 2)
    (hc : χ (p : ℕ) = 0) : quadraticPrimeSplittingAt K χ p := by
  classical
  have hs : RingOfIntegers.monicFactorsMod θ p = {Polynomial.X - Polynomial.C r} := by
    change (UniqueFactorizationMonoid.normalizedFactors _).toFinset = _
    rw [hf, linear_square_factors, Multiset.toFinset_replicate]
    rfl
  let U : RingOfIntegers.monicFactorsMod θ p :=
    ⟨Polynomial.X - Polynomial.C r, hs.symm ▸ Finset.mem_singleton_self _⟩
  let P := (NumberField.Ideal.primesOverSpanEquivMonicFactorsMod hp).symm U
  have hp0 : Ideal.span {(p : ℤ)} ≠ ⊥ :=
    mt Ideal.span_singleton_eq_bot.mp (Int.natCast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  refine
    Or.inl
      ⟨hc, (P : Ideal (NumberField.RingOfIntegers K)), Ideal.prime_of_mem_primesOver hp0 P.property,
        ?_, ?_⟩
  · rw [principal_prime_eq_prod_monicFactors K θ p hp]
    have he : ∀ V : RingOfIntegers.monicFactorsMod θ p, V = U := by
      intro V
      apply Subtype.ext
      exact Finset.mem_singleton.mp (hs ▸ V.property)
    rw [Fintype.prod_eq_single U (fun V hn => False.elim (hn (he V)))]
    exact
      congrArg ((P : Ideal (NumberField.RingOfIntegers K)) ^ ·) (hf ▸ linear_square_multiplicity r)
  · exact
      (absNorm_primeIdeal_of_monicFactor K θ p hp U).trans
        ((congrArg (p ^ ·) (Polynomial.natDegree_X_sub_C r)).trans (pow_one p))

/-- If the reduced minimal polynomial has two distinct linear factors and the character
has value one at `p`, with `p` not dividing the generator's exponent, the principal
ideal splits into two coprime prime ideals of norm `p`.
Distinct factors give distinct maximal ideals, and their multiplicities are one.
This supplies the split input to ideal counting. -/
theorem quadraticPrimeSplittingAt_of_reduced_distinct_linear_factors (K : Type) [Field K]
    [NumberField K] {q : ℕ} (χ : DirichletCharacter ℂ q) (θ : NumberField.RingOfIntegers K) (p : ℕ)
    [Fact p.Prime] (hp : ¬p ∣ RingOfIntegers.exponent θ) (r s : ZMod p) (hrs : r ≠ s)
    (hf :
      (minpoly ℤ θ).map (Int.castRingHom (ZMod p)) =
        (Polynomial.X - Polynomial.C r) * (Polynomial.X - Polynomial.C s))
    (hc : χ (p : ℕ) = 1) : quadraticPrimeSplittingAt K χ p := by
  classical
  have hs :
    RingOfIntegers.monicFactorsMod θ p =
      {Polynomial.X - Polynomial.C r, Polynomial.X - Polynomial.C s} := by
    change (UniqueFactorizationMonoid.normalizedFactors _).toFinset = _
    rw [hf, linear_product_factors]
    simp only [Multiset.toFinset_add, Multiset.toFinset_singleton, Finset.singleton_union]
  let U : RingOfIntegers.monicFactorsMod θ p :=
    ⟨Polynomial.X - Polynomial.C r, hs.symm ▸ Finset.mem_insert_self _ _⟩
  let V : RingOfIntegers.monicFactorsMod θ p :=
    ⟨Polynomial.X - Polynomial.C s,
      hs.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩
  let e := NumberField.Ideal.primesOverSpanEquivMonicFactorsMod hp
  let P := e.symm U
  let Q := e.symm V
  have hp0 : Ideal.span {(p : ℤ)} ≠ ⊥ :=
    mt Ideal.span_singleton_eq_bot.mp (Int.natCast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  have huv : U ≠ V := fun h ↦
    hrs (Polynomial.C_injective (sub_right_inj.mp (congrArg Subtype.val h)))
  have hpq : (P : Ideal (NumberField.RingOfIntegers K)) ≠ Q := fun h ↦
    huv (e.symm.injective (Subtype.ext h))
  refine
    Or.inr
      (Or.inr
        ⟨hc, P, Q, Ideal.prime_of_mem_primesOver hp0 P.property,
          Ideal.prime_of_mem_primesOver hp0 Q.property, ?_, ?_, ?_, ?_⟩)
  · exact
      Ideal.isCoprime_iff_sup_eq.mpr
        ((P.property.1.isMaximal (Ideal.ne_bot_of_mem_primesOver hp0 P.property)).coprime_of_ne
          (Q.property.1.isMaximal (Ideal.ne_bot_of_mem_primesOver hp0 Q.property)) hpq)
  · rw [principal_prime_eq_prod_monicFactors K θ p hp]
    have hall : ∀ W : RingOfIntegers.monicFactorsMod θ p, W = U ∨ W = V := by
      intro W
      have hw := W.property
      simp only [hs, Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with hr | hs'
      · exact Or.inl (Subtype.ext hr)
      · exact Or.inr (Subtype.ext hs')
    rw [Finset.prod_eq_mul_of_mem U V (Finset.mem_univ _) (Finset.mem_univ _) huv
        (fun W _ hn ↦ False.elim ((hall W).elim hn.1 hn.2))]
    have hu : multiplicity U.val ((minpoly ℤ θ).map (Int.castRingHom (ZMod p))) = 1 :=
      hf ▸ linear_product_multiplicity r s hrs
    have hv : multiplicity V.val ((minpoly ℤ θ).map (Int.castRingHom (ZMod p))) = 1 := by
      rw [hf, mul_comm]
      exact linear_product_multiplicity s r hrs.symm
    rw [hu, hv, pow_one, pow_one]
  · exact
      (absNorm_primeIdeal_of_monicFactor K θ p hp U).trans
        ((congrArg (p ^ ·) (Polynomial.natDegree_X_sub_C r)).trans (pow_one p))
  · exact
      (absNorm_primeIdeal_of_monicFactor K θ p hp V).trans
        ((congrArg (p ^ ·) (Polynomial.natDegree_X_sub_C s)).trans (pow_one p))

end PseudoPrime.NumberTheory
