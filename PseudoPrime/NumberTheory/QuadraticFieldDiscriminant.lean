/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.QuadraticFieldArithmetic

/-!
# Fundamental discriminants of quadratic number fields

Prove that the actual discriminant of a degree-two number field is fundamental by using
integral quadratic coordinates to rule out additional integral elements that a nonfundamental
discriminant would produce.
-/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- If an integral linear expression in the quadratic generator divided by `p` is integral,
then its generator coefficient is divisible by `p`. Lift the integral quotient back into
the ring of integers, transport the equality to the quadratic algebra, and compare
imaginary coordinates. This detects impossible enlargements of the integral order. -/
private theorem integral_div_generator_dvd (K : Type) [Field K] [NumberField K] (a b : ℤ)
    (f : NumberField.RingOfIntegers K ≃ₐ[ℤ] QuadraticAlgebra ℤ a b) (r t p : ℤ) (hp : p ≠ 0)
    (hi :
      IsIntegral ℤ
        (((r : K) * (algebraMap (NumberField.RingOfIntegers K) K (f.symm QuadraticAlgebra.omega)) +
            t) /
          p)) :
    p ∣ r := by
  obtain ⟨y, hy⟩ := (IsIntegralClosure.isIntegral_iff (A := NumberField.RingOfIntegers K)).mp hi
  have he :
    (p : K) * algebraMap (NumberField.RingOfIntegers K) K y =
      (r : K) * algebraMap (NumberField.RingOfIntegers K) K (f.symm QuadraticAlgebra.omega) +
        t := by
    rw [hy]
    field_simp [Int.cast_ne_zero.mpr hp]
  have ho :
    (p : NumberField.RingOfIntegers K) * y =
      (r : NumberField.RingOfIntegers K) * f.symm QuadraticAlgebra.omega + t := by
    apply IsFractionRing.injective (NumberField.RingOfIntegers K) K
    simpa only [map_mul, map_add, map_intCast] using he
  have hh := congrArg QuadraticAlgebra.im (congrArg f ho)
  simp only [map_mul, map_add, map_intCast, f.apply_symm_apply, QuadraticAlgebra.im_mul,
    QuadraticAlgebra.im_add, QuadraticAlgebra.im_intCast, QuadraticAlgebra.re_intCast,
    QuadraticAlgebra.re_omega, QuadraticAlgebra.im_omega, zero_mul, mul_zero, add_zero,
    mul_one] at hh
  exact ⟨(f y).im, hh.symm⟩

/-- Transport the defining quadratic relation to the ambient number field.
The generator of the entire ring of integers satisfies `w² = a + bw`.
This relation is used to construct integral square roots from a discriminant square divisor. -/
private theorem model_generator_sq (K : Type) [Field K] [NumberField K] (a b : ℤ)
    (f : NumberField.RingOfIntegers K ≃ₐ[ℤ] QuadraticAlgebra ℤ a b) :
    (algebraMap (NumberField.RingOfIntegers K) K (f.symm QuadraticAlgebra.omega)) ^ 2 =
      (a : K) +
        (b : K) * algebraMap (NumberField.RingOfIntegers K) K (f.symm QuadraticAlgebra.omega) := by
  have h :=
    congrArg f.symm (QuadraticAlgebra.omega_mul_omega_eq_algebraMap (R := ℤ) (a := a) (b := b))
  have h2 := congrArg (algebraMap (NumberField.RingOfIntegers K) K) h
  simpa only [map_mul, map_add, AlgEquiv.commutes, algebraMap_int_eq, Int.coe_castRingHom,
    map_intCast, sq] using h2

/-- The element `2w - b` has square equal to the integral quadratic discriminant.
Expand its square and substitute the generator relation. If a nonzero integer `p` has
`p²` dividing the discriminant, division by `p` gives an element with integral square.
This is the square identity used to exclude such divisors unless `p` divides two. -/
private theorem model_discr_sqrt_sq (K : Type) [Field K] [NumberField K] (a b : ℤ)
    (f : NumberField.RingOfIntegers K ≃ₐ[ℤ] QuadraticAlgebra ℤ a b) :
    (2 * algebraMap (NumberField.RingOfIntegers K) K (f.symm QuadraticAlgebra.omega) - (b : K)) ^
        2 =
      (b : K) ^ 2 + 4 * (a : K) := by
  let w := algebraMap (NumberField.RingOfIntegers K) K (f.symm QuadraticAlgebra.omega)
  have h : w ^ 2 = (a : K) + (b : K) * w := model_generator_sq K a b f
  change (2 * w - b) ^ 2 = _
  calc
    (2 * w - b) ^ 2 = 4 * w ^ 2 - 4 * (b : K) * w + (b : K) ^ 2 := by ring
    _ = (b : K) ^ 2 + 4 * (a : K) := by
      rw [h]; ring

/-- A nonzero integer whose square divides the discriminant of an integral quadratic model
divides two. Dividing `2w - b` by that integer gives an element with integral square,
hence an integral element; comparison of integral generator coordinates gives the divisibility. -/
private theorem model_discr_sq_dvd_two (K : Type) [Field K] [NumberField K] (a b : ℤ)
    (f : NumberField.RingOfIntegers K ≃ₐ[ℤ] QuadraticAlgebra ℤ a b) (p : ℤ) (hp : p ≠ 0)
    (hd : p ^ 2 ∣ b ^ 2 + 4 * a) : p ∣ 2 := by
  obtain ⟨e, he⟩ := hd
  let w := algebraMap (NumberField.RingOfIntegers K) K (f.symm QuadraticAlgebra.omega)
  have hs : (2 * w - (b : K)) ^ 2 = (p : K) ^ 2 * (e : K) := by
    rw [model_discr_sqrt_sq K a b f]
    exact_mod_cast he
  have hx : ((2 * w - (b : K)) / (p : K)) ^ 2 = (e : K) := by
    rw [div_pow, hs]
    field_simp [Int.cast_ne_zero.mpr hp]
  have hi : IsIntegral ℤ ((2 * w - (b : K)) / (p : K)) := by
    apply IsIntegral.of_pow (show 0 < (2 : ℕ) from by norm_num only)
    rw [hx]
    exact isIntegral_algebraMap (x := e)
  have hh := integral_div_generator_dvd K a b f 2 (-b) p hp
  apply hh
  simpa only [Int.cast_ofNat, Int.cast_neg, sub_eq_add_neg] using hi

/-- If `z² = 4c + 1` with integer `c`, then `(z + 1) / 2` is integral.
It satisfies the monic polynomial `X² - X - c`. This supplies the larger integral order
that would occur if a quadratic discriminant divided by four were congruent to one. -/
private theorem integral_half_of_sq_eq_four_mul_add_one (K : Type) [Field K] [NumberField K] (z : K)
    (c : ℤ) (hz : z ^ 2 = 4 * (c : K) + 1) : IsIntegral ℤ ((z + 1) / 2) := by
  let x := (z + 1) / 2
  have hx : x ^ 2 - x = (c : K) := by
    change ((z + 1) / 2) ^ 2 - (z + 1) / 2 = _
    field_simp
    linear_combination hz
  have hm : ((Polynomial.X ^ 2 - Polynomial.C c) - Polynomial.X : Polynomial ℤ).Monic := by
    apply (Polynomial.monic_X_pow_sub_C c (show (2 : ℕ) ≠ 0 from by norm_num only)).sub_of_left
    rw [Polynomial.degree_X, Polynomial.degree_X_pow_sub_C (show 0 < (2 : ℕ) from by norm_num only)]
    norm_num only
  refine ⟨(Polynomial.X ^ 2 - Polynomial.C c) - Polynomial.X, hm, ?_⟩
  change (Polynomial.aeval x) ((Polynomial.X ^ 2 - Polynomial.C c) - Polynomial.X) = 0
  simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, algebraMap_int_eq,
    Int.coe_castRingHom]
  linear_combination hx

/-- For an integral quadratic model with discriminant `4e`, the integer `e` is not one modulo four.
Write the trace coefficient as `2t`, so `(w - t)² = e`. If `e = 4c + 1`, then
`(w - t + 1) / 2` is integral, contradicting divisibility of its generator coefficient
one by two. -/
private theorem quadratic_half_root_not_one_mod_four (K : Type) [Field K] [NumberField K]
    (a b e : ℤ) (f : NumberField.RingOfIntegers K ≃ₐ[ℤ] QuadraticAlgebra ℤ a b)
    (hd : b ^ 2 + 4 * a = 4 * e) : e % 4 ≠ 1 := by
  intro he
  have hb : (2 : ℤ) ∣ b := by
    apply Int.prime_two.dvd_of_dvd_pow (n := 2)
    refine ⟨2 * (e - a), ?_⟩
    nlinarith only [hd]
  obtain ⟨t, ht⟩ := hb
  have heq : e = t ^ 2 + a := by
    rw [ht] at hd
    nlinarith only [hd]
  let w := algebraMap (NumberField.RingOfIntegers K) K (f.symm QuadraticAlgebra.omega)
  have hw : w ^ 2 = (a : K) + (b : K) * w := model_generator_sq K a b f
  have htK : (b : K) = 2 * (t : K) := by exact_mod_cast ht
  have hβ : (w - (t : K)) ^ 2 = (e : K) := by
    rw [heq, Int.cast_add, Int.cast_pow]
    calc
      (w - (t : K)) ^ 2 = w ^ 2 - 2 * t * w + (t : K) ^ 2 := by ring
      _ = (t : K) ^ 2 + a := by
        rw [hw, htK]; ring
  let c := e / 4
  have hc : e = 4 * c + 1 := by
    have h := Int.mul_ediv_add_emod e 4
    rw [he] at h
    exact h.symm
  have hcK : (e : K) = 4 * (c : K) + 1 := by exact_mod_cast hc
  have hi := integral_half_of_sq_eq_four_mul_add_one K (w - (t : K)) c (hβ.trans hcK)
  have hp := integral_div_generator_dvd K a b f 1 (1 - t) 2 (show (2 : ℤ) ≠ 0 from by norm_num only)
  have hi2 : IsIntegral ℤ (((1 : K) * w + ((1 - t : ℤ) : K)) / 2) := by
    convert hi using 1
    simp only [Int.cast_sub, Int.cast_one, one_mul]
    ring
  have hbad : (2 : ℤ) ∣ 1 := hp (by simpa only [Int.cast_one, Int.cast_ofNat] using hi2)
  norm_num only at hbad

/-- The discriminant of every degree-two number field is a fundamental discriminant.
Use the integral quadratic model for the congruence condition. If `p²` divides the
discriminant for a nonzero integer `p`, then `p` divides two. This excludes odd prime
squares and discriminants divisible by sixteen.
A putative quotient by four congruent to one would give an extra integral half-generator.
These coordinate arguments prove primitivity without assumptions on the discriminant sign
and supply the arithmetic discriminant required for the quadratic Dirichlet character. -/
theorem quadratic_discr_isFundamental (K : Type) [Field K] [NumberField K]
    (hdeg : Module.finrank ℚ K = 2) : Int.IsFundamentalDiscr (NumberField.discr K) := by
  obtain ⟨a, b, f, hd⟩ := quadratic_ringOfIntegers_model K hdeg
  refine ⟨quadratic_discr_emod_four K hdeg, ?_, ?_⟩
  · intro e he
    constructor
    · intro h4
      obtain ⟨c, hc⟩ := h4
      have hsq : (4 : ℤ) ^ 2 ∣ b ^ 2 + 4 * a := by
        refine ⟨c, ?_⟩
        nlinarith only [hd, he, hc]
      have hbad := model_discr_sq_dvd_two K a b f 4 (show (4 : ℤ) ≠ 0 from by norm_num only) hsq
      norm_num only at hbad
    · apply quadratic_half_root_not_one_mod_four K a b e f
      exact hd.symm.trans he
  · intro p hp hodd hsq
    have hsq2 : (p : ℤ) ^ 2 ∣ b ^ 2 + 4 * a := hd ▸ hsq
    have hdiv := model_discr_sq_dvd_two K a b f p (Int.natCast_ne_zero.mpr hp.ne_zero) hsq2
    have hdivN : p ∣ 2 := by exact_mod_cast hdiv
    have heq : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdivN
    exact hodd.not_two_dvd_nat (heq ▸ dvd_rfl)

end PseudoPrime.NumberTheory
