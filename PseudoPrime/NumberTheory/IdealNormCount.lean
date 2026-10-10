/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.NumberField.Ideal.Basic
public import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# Multiplicativity of integral ideal counts

Decompose ideals with coprime norm factors by adding the principal ideals of those factors.
Use the resulting equivalence of norm fibers to reduce a character divisor-sum identity
to prime-power identities, as needed for quadratic Dedekind zeta factorization.
-/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- Coprime natural numbers generate comaximal ideals in a ring of integers.
Transport their integral Bezout identity to the ring. This separates the two norm factors. -/
private theorem normCount_span_coprime (K : Type) [Field K] [NumberField K] {m n : ℕ}
    (h : m.Coprime n) :
    (Ideal.span {(m : NumberField.RingOfIntegers K)}) ⊔
        Ideal.span {(n : NumberField.RingOfIntegers K)} =
      ⊤ := by
  apply Ideal.isCoprime_iff_sup_eq.mp
  apply (Ideal.isCoprime_span_singleton_iff _ _).mpr
  simpa only [map_natCast] using h.isCoprime.map (Int.castRingHom (NumberField.RingOfIntegers K))

/-- If two comaximal ideals have product contained in `I`, adding them separately to `I`
gives two ideals whose product is `I`. Expand both products for one inclusion and use
comaximality for the other. This is the algebraic decomposition used in norm counting. -/
private theorem normCount_split_product {R : Type} [CommRing R] (I A B : Ideal R) (h : A ⊔ B = ⊤)
    (hab : A * B ≤ I) : (I ⊔ A) * (I ⊔ B) = I := by
  apply le_antisymm
  · rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup]
    exact sup_le (sup_le Ideal.mul_le_left Ideal.mul_le_left) (sup_le Ideal.mul_le_right hab)
  · have hi : I * (A ⊔ B) = I := by rw [h, ← Ideal.one_eq_top, mul_one]
    calc
      I = I * A ⊔ I * B := hi.symm.trans (Ideal.mul_sup _ _ _)
      _ ≤ (I ⊔ A) * (I ⊔ B) :=
        sup_le
          (by
            rw [mul_comm]; exact Ideal.mul_mono le_sup_right le_sup_left)
          (Ideal.mul_mono le_sup_left le_sup_right)

/-- For an ideal of norm `m * n` with coprime `m` and `n`, its sum with the ideal `(m)`
has norm dividing `m`. Its norm divides both `m * n` and a power of `m`;
coprimality removes the factor `n`. This bounds the norm of the first component. -/
private theorem normCount_split_norm_dvd (K : Type) [Field K] [NumberField K] {m n : ℕ}
    (h : m.Coprime n) (I : Ideal (NumberField.RingOfIntegers K)) (hi : Ideal.absNorm I = m * n) :
    Ideal.absNorm (I ⊔ Ideal.span {(m : NumberField.RingOfIntegers K)}) ∣ m := by
  have hdiv :=
    Ideal.absNorm_dvd_absNorm_of_le
      (le_sup_left : I ≤ I ⊔ Ideal.span {(m : NumberField.RingOfIntegers K)})
  rw [hi] at hdiv
  have hpow :=
    Ideal.absNorm_dvd_absNorm_of_le
      (le_sup_right :
        Ideal.span {(m : NumberField.RingOfIntegers K)} ≤
          I ⊔ Ideal.span {(m : NumberField.RingOfIntegers K)})
  rw [Ideal.absNorm_span_natCast] at hpow
  exact ((h.pow_left _).of_dvd_left hpow).dvd_mul_right.mp hdiv

/-- An ideal of norm `m * n` splits as the product of its sums with `(m)` and `(n)`
when `m` and `n` are coprime. The norm belongs to the ideal, so `(m)(n)` is contained
in it. Apply the comaximal decomposition to obtain the inverse to ideal multiplication. -/
theorem normCount_split_product_nat (K : Type) [Field K] [NumberField K] {m n : ℕ} (h : m.Coprime n)
    (I : Ideal (NumberField.RingOfIntegers K)) (hi : Ideal.absNorm I = m * n) :
    (I ⊔ Ideal.span {(m : NumberField.RingOfIntegers K)}) *
        (I ⊔ Ideal.span {(n : NumberField.RingOfIntegers K)}) =
      I := by
  apply normCount_split_product _ _ _ (normCount_span_coprime K h)
  rw [Ideal.span_singleton_mul_span_singleton, ← Nat.cast_mul, ← hi]
  exact Ideal.span_singleton_absNorm_le I

/-- For coprime `m` and `n`, adding `(m)` to an ideal of norm `m * n` gives norm `m`.
The component norms divide the intended factors; norm multiplicativity and coprimality
give the reverse divisibility. This places the first component in the required norm fiber. -/
theorem normCount_split_norm (K : Type) [Field K] [NumberField K] {m n : ℕ} (h : m.Coprime n)
    (I : Ideal (NumberField.RingOfIntegers K)) (hi : Ideal.absNorm I = m * n) :
    Ideal.absNorm (I ⊔ Ideal.span {(m : NumberField.RingOfIntegers K)}) = m := by
  have hm := normCount_split_norm_dvd K h I hi
  have hn := normCount_split_norm_dvd K h.symm I (hi.trans (mul_comm m n))
  have hp := congrArg Ideal.absNorm (normCount_split_product_nat K h I hi)
  rw [map_mul, hi] at hp
  have hmdiv :
    m ∣
      Ideal.absNorm (I ⊔ Ideal.span {(m : NumberField.RingOfIntegers K)}) *
        Ideal.absNorm (I ⊔ Ideal.span {(n : NumberField.RingOfIntegers K)}) := by
    rw [hp]; exact dvd_mul_right m n
  exact Nat.dvd_antisymm hm ((h.of_dvd_right hn).dvd_mul_right.mp hmdiv)

/-- Adding `(m)` to the product of ideals of coprime norms `m` and `n` recovers the
first ideal. Each ideal contains its norm, and the second is comaximal with `(m)`.
This is the left inverse needed for the norm-fiber multiplication equivalence. -/
private theorem normCount_recover_left (K : Type) [Field K] [NumberField K] {m n : ℕ}
    (h : m.Coprime n) (I J : Ideal (NumberField.RingOfIntegers K)) (hi : Ideal.absNorm I = m)
    (hj : Ideal.absNorm J = n) : I * J ⊔ Ideal.span {(m : NumberField.RingOfIntegers K)} = I := by
  have hm : Ideal.span {(m : NumberField.RingOfIntegers K)} ≤ I := by
    rw [← hi]; exact Ideal.span_singleton_absNorm_le I
  have hn : Ideal.span {(n : NumberField.RingOfIntegers K)} ≤ J := by
    rw [← hj]; exact Ideal.span_singleton_absNorm_le J
  have hc : Ideal.span {(m : NumberField.RingOfIntegers K)} ⊔ J = ⊤ :=
    eq_top_iff.mpr ((normCount_span_coprime K h).ge.trans (sup_le_sup le_rfl hn))
  calc
    _ = Ideal.span {(m : NumberField.RingOfIntegers K)} ⊔ I * J := sup_comm _ _
    _ = Ideal.span {(m : NumberField.RingOfIntegers K)} ⊔ I := Ideal.sup_mul_eq_of_coprime_right hc
    _ = I := sup_eq_right.mpr hm

/-- For coprime natural numbers `m` and `n`, ideal multiplication is an equivalence
from the product of the norm-`m` and norm-`n` fibers to the norm-`m * n` fiber.
The inverse sends `I` to its sums with `(m)` and `(n)`. The component norms and
inverse identities follow from comaximality and norm multiplicativity.
This counts ideals without choosing their prime ideal factorizations. -/
def idealNormFiberMulEquiv (K : Type) [Field K] [NumberField K] (m n : ℕ) (h : m.Coprime n) :
    ({ I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = m } ×
        { I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = n }) ≃
      { I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = m * n }
    where
  toFun x := ⟨x.1.val * x.2.val, by rw [map_mul, x.1.property, x.2.property]⟩
  invFun x :=
    (⟨x.val ⊔ Ideal.span {(m : NumberField.RingOfIntegers K)},
        normCount_split_norm K h x.val x.property⟩,
      ⟨x.val ⊔ Ideal.span {(n : NumberField.RingOfIntegers K)},
        normCount_split_norm K h.symm x.val (x.property.trans (mul_comm _ _))⟩)
  left_inv x := by
    apply Prod.ext
    · exact Subtype.ext (normCount_recover_left K h x.1.val x.2.val x.1.property x.2.property)
    · apply Subtype.ext
      change x.1.val * x.2.val ⊔ Ideal.span {(n : NumberField.RingOfIntegers K)} = x.2.val
      rw [mul_comm]
      exact normCount_recover_left K h.symm x.2.val x.1.val x.2.property x.1.property
  right_inv x := Subtype.ext (normCount_split_product_nat K h x.val x.property)

/-- For coprime `m` and `n`, the number of integral ideals of norm `m * n` equals
the product of the counts for norms `m` and `n`. Take natural cardinalities of
the norm-fiber multiplication equivalence. This gives the multiplicativity needed
to reduce Dedekind zeta coefficients to prime-power coefficients. -/
theorem card_ideal_absNorm_mul_of_coprime (K : Type) [Field K] [NumberField K] (m n : ℕ)
    (h : m.Coprime n) :
    Nat.card { I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = m * n } =
      Nat.card { I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = m } *
        Nat.card { I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = n } := by
  rw [← Nat.card_congr (idealNormFiberMulEquiv K m n h), Nat.card_prod]

/-- The unit ideal is the unique integral ideal of norm one in a number field.
Use the norm-one characterization to prove the fiber is inhabited and subsingleton.
This supplies the unit value for multiplicativity of ideal counts. -/
theorem card_ideal_absNorm_one (K : Type) [Field K] [NumberField K] :
    Nat.card { I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = 1 } = 1 := by
  apply Nat.card_eq_one_iff_unique.mpr
  refine ⟨⟨?_⟩, ⟨⟨⊤, Ideal.absNorm_top⟩⟩⟩
  intro I J
  apply Subtype.ext
  exact (Ideal.absNorm_eq_one_iff.mp I.property).trans (Ideal.absNorm_eq_one_iff.mp J.property).symm

/-- The complex-valued integral-ideal count, with value zero at zero, is a
multiplicative arithmetic function. Norm one has exactly one ideal and coprime norm
fibers multiply bijectively. This permits comparison with a character divisor sum
by checking only prime powers. -/
theorem isMultiplicative_idealNormCount (K : Type) [Field K] [NumberField K] :
    ArithmeticFunction.IsMultiplicative
      (toArithmeticFunction
        (fun n ↦
          (Nat.card { I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = n } : ℂ))) := by
  apply ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr
  constructor
  · change
      (if (1 : ℕ) = 0 then 0
        else (Nat.card { I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = 1 } : ℂ)) =
        1
    rw [ite_eq_right Nat.one_ne_zero, card_ideal_absNorm_one, Nat.cast_one]
  · intro m n hm hn hc
    change
      (if m * n = 0 then 0
        else
          (Nat.card { I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = m * n } : ℂ)) =
        (if m = 0 then 0 else _) * (if n = 0 then 0 else _)
    rw [ite_eq_right (mul_ne_zero hm hn), ite_eq_right hm, ite_eq_right hn,
      card_ideal_absNorm_mul_of_coprime K m n hc, Nat.cast_mul]

/-- For every natural `n`, the Dirichlet convolution of the zeta arithmetic function
and a character is its sum over the second entries of `n.divisorsAntidiagonal`.
Each divisor pair has nonzero entries; at zero the pair set is empty. Thus the
arithmetic-function zero convention does not affect this coefficient formula. -/
private theorem normCount_character_convolution {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) :
    ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) * toArithmeticFunction (fun n ↦ χ n)) n =
      ∑ d ∈ n.divisorsAntidiagonal, χ (d.2 : ℕ) := by
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_congr rfl
  intro d hd
  rw [← χ.apply_eq_toArithmeticFunction_apply (Nat.right_ne_zero_of_mem_divisorsAntidiagonal hd),
    ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply,
    ite_eq_right (Nat.left_ne_zero_of_mem_divisorsAntidiagonal hd), Nat.cast_one, one_mul]

/-- If the integral-ideal count equals the divisor sum of a fixed character at every
prime power, it equals that sum at every positive integer. The normalized ideal count
and the convolution of zeta with the character are multiplicative arithmetic functions;
the prime-power comparison theorem identifies them. This reduces the arithmetic premise
of quadratic Dedekind factorization and the class-number bounds to local counting. -/
theorem ideal_count_eq_divisor_sum_of_prime_power_count (K : Type) [Field K] [NumberField K] {q : ℕ}
    (χ : DirichletCharacter ℂ q)
    (hp :
      ∀ p k : ℕ,
        p.Prime →
          (Nat.card { I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = p ^ k } : ℂ) =
            ∑ d ∈ (p ^ k).divisorsAntidiagonal, χ (d.2 : ℕ))
    (n : ℕ) (hn : n ≠ 0) :
    (Nat.card { I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = n } : ℂ) =
      ∑ d ∈ n.divisorsAntidiagonal, χ (d.2 : ℕ) := by
  let f :=
    toArithmeticFunction
      (fun n ↦ (Nat.card { I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = n } : ℂ))
  let g := (ArithmeticFunction.zeta : ArithmeticFunction ℂ) * toArithmeticFunction (fun n ↦ χ n)
  have hg : g.IsMultiplicative :=
    ArithmeticFunction.isMultiplicative_zeta.natCast.mul χ.isMultiplicative_toArithmeticFunction
  have he : f = g :=
    (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers f
          (isMultiplicative_idealNormCount K) g hg).mpr
      (by
        intro p k hprime
        change (if p ^ k = 0 then 0 else _) = g (p ^ k)
        rw [ite_eq_right (pow_ne_zero k hprime.ne_zero)]
        exact (hp p k hprime).trans (normCount_character_convolution χ (p ^ k)).symm)
  have h := DFunLike.congr_fun he n
  change (if n = 0 then 0 else _) = g n at h
  rw [ite_eq_right hn] at h
  exact h.trans (normCount_character_convolution χ n)

end PseudoPrime.NumberTheory
