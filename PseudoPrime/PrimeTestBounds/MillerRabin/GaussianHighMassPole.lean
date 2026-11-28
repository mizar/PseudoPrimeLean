/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighMassPolynomial
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighMassPolynomial
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighKernelData
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! # Rational continuation and pole value of the high Gaussian absolute mass -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Algebraic evaluation of the two polynomial parts over a commutative ring. -/
private theorem power_parts_algebra {R : Type*} [CommRing R] (f : ℚ →+* R) (a : ℚ) (z : R) (k : ℕ) :
    let u := f a ^ 2 - z ^ 2
    let (A, B) := powerParts a k
    A.eval₂ f u + z * B.eval₂ f u = (z + f a) ^ k := by
  induction k with
  | zero =>
    simp only [powerParts, Polynomial.eval₂_one, Polynomial.eval₂_zero, mul_zero, add_zero,
      pow_zero]
  | succ k ih =>
    rcases h : powerParts a k with ⟨A, B⟩
    rw [h] at ih
    rw [powerParts, h]
    dsimp only at ih ⊢
    rw [pow_succ (z + f a) k, ← ih]
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_C,
      Polynomial.eval₂_X, Polynomial.eval₂_pow, map_pow]
    ring

/-- The polynomial evaluation splits into the part even in `z` and `z` times an even part. -/
private theorem polynomial_parts_algebra {R : Type*} [CommRing R] (f : ℚ →+* R) (a : ℚ)
    (P : Polynomial ℚ) (z : R) :
    let u := f a ^ 2 - z ^ 2
    let A := (polynomialParts a P).1
    let B := (polynomialParts a P).2
    A.eval₂ f u + z * B.eval₂ f u = P.eval₂ f (z + f a) := by
  dsimp only [polynomialParts]
  rw [Polynomial.eval₂_eq_sum_range (p := P)]
  simp only [Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul, Polynomial.eval₂_C, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [← mul_left_comm (f (P.coeff k)), ← mul_add]
  congr 1
  exact power_parts_algebra f a z k

/-- At `u = a² - z²`, the rational squared-norm polynomial extends as the
product of the original evaluations at the reflected points `a + z` and `a - z`. -/
public theorem norm_sq_polynomial_reflect {R : Type*} [CommRing R] (f : ℚ →+* R) (a : ℚ)
    (P : Polynomial ℚ) (z : R) :
    (normSqPolynomial a P).eval₂ f (f a ^ 2 - z ^ 2) =
      P.eval₂ f (z + f a) * P.eval₂ f (-z + f a) := by
  have hpos := polynomial_parts_algebra f a P z
  have hneg := polynomial_parts_algebra f a P (-z)
  dsimp only at hpos hneg
  simp only [neg_sq] at hneg
  rw [← hpos, ← hneg]
  simp only [normSqPolynomial, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
    Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C, map_pow]
  ring

/-- Rational value of the continued absolute mass at the pole of the principal term. -/
public noncomputable def HighGaussianKernel.massPole (K : HighGaussianKernel) : ℚ :=
  K.normalization *
      (normSqPolynomial K.pole K.polynomial).eval₂ (RingHom.id ℚ) (K.pole ^ 2 - (1 / 2) ^ 2) /
    (K.pole ^ 2 - (1 / 2) ^ 2) ^ (K.degree + 2)

/-- The pole term is the product of the two reflected compact polynomial values,
as in the manuscript's formula (H11). -/
public theorem high_gaussian_mass_pole_product (K : HighGaussianKernel) :
    K.massPole =
      K.normalization * K.polynomial.eval₂ (RingHom.id ℚ) (1 / 2 + K.pole) *
          K.polynomial.eval₂ (RingHom.id ℚ) (-(1 / 2) + K.pole) /
        (K.pole ^ 2 - (1 / 2) ^ 2) ^ (K.degree + 2) := by
  unfold HighGaussianKernel.massPole
  have h := norm_sq_polynomial_reflect (RingHom.id ℚ) K.pole K.polynomial (1 / 2)
  simp only [RingHom.id_apply] at h
  rw [h, mul_assoc]

/-- Evaluation of the original compact form using its rational coefficients. -/
private def compactValue (K : HighGaussianKernel) (w : ℚ) : ℚ :=
  let v := coefficientTicks K
  ∑ j ∈ Finset.range (K.degree + 1),
    ((v[j]?.getD 0 : ℤ) : ℚ) / (v.sum : ℚ) * w ^ (K.degree - j) * (w - 2 * K.pole) ^ j

/-- The rational evaluator reproduces the compact kernel polynomial at every argument. -/
private theorem compact_value_eq (K : HighGaussianKernel) (w : ℚ) :
    K.polynomial.eval₂ (RingHom.id ℚ) w = compactValue K w := by
  simp only [HighGaussianKernel.polynomial, compactValue, Polynomial.eval₂_finsetSum,
    Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_pow,
    Polynomial.eval₂_sub, RingHom.id_apply]

/-- The pole value for K186 lies between the two rational endpoints in (H11). -/
public theorem gaussian_k186_mass_pole_bounds :
    (125564 / 10000 : ℚ) < HighGaussianKernel.k186.massPole ∧
      HighGaussianKernel.k186.massPole < 125565 / 10000 := by
  rw [high_gaussian_mass_pole_product, compact_value_eq, compact_value_eq]
  decide +kernel

/-- The pole value for K196 lies between the two rational endpoints in (H11). -/
public theorem gaussian_k196_mass_pole_bounds :
    (22625 / 10000 : ℚ) < HighGaussianKernel.k196.massPole ∧
      HighGaussianKernel.k196.massPole < 22627 / 10000 := by
  rw [high_gaussian_mass_pole_product, compact_value_eq, compact_value_eq]
  decide +kernel

/-- Evaluation commutes with a coefficient-compatible coefficient-ring map. -/
private theorem eval_cast_map {R S : Type*} [CommRing R] [CommRing S] (f : ℚ →+* R) (g : R →+* S)
    (P : Polynomial ℚ) (x : R) : g (P.eval₂ f x) = P.eval₂ (g.comp f) (g x) := by
  simp only [Polynomial.eval₂_eq_sum_range, map_sum, map_mul, map_pow, RingHom.comp_apply]

/-- The rational continuation of the absolute high Gaussian mass, with possible
poles at the two opposite shifts. -/
public noncomputable def HighGaussianKernel.massExtension (K : HighGaussianKernel) (z : ℂ) : ℂ :=
  let u := (K.pole : ℂ) ^ 2 - z ^ 2
  (K.normalization : ℂ) * (normSqPolynomial K.pole K.polynomial).eval₂ (Rat.castHom ℂ) u /
    u ^ (K.degree + 2)

/-- The rational continuation restricts to the absolute kernel on the critical line. -/
public theorem high_gaussian_mass_extension_line (K : HighGaussianKernel) (t : ℝ) :
    K.massExtension (Complex.I * (t : ℂ)) =
      ((‖∑ j ∈ Finset.range (2 * K.degree + 1),
              (K.expandedCoeff j : ℂ) * Complex.exp (5 * (Complex.I * (t : ℂ))) /
                (Complex.I * (t : ℂ) + (K.pole : ℂ)) ^ (K.logPower j + 1)‖ :
          ℝ) :
        ℂ) := by
  have hu :
    (K.pole : ℂ) ^ 2 - (Complex.I * (t : ℂ)) ^ 2 = (((K.pole : ℝ) ^ 2 + t ^ 2 : ℝ) : ℂ) := by
    simp only [Complex.ofReal_add, Complex.ofReal_pow, Complex.ofReal_ratCast, mul_pow,
      Complex.I_sq, neg_one_mul, sub_neg_eq_add]
  rw [high_gaussian_norm_rational, HighGaussianKernel.massExtension]
  dsimp only
  rw [hu]
  simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_ratCast]
  congr 2
  have hc :=
    eval_cast_map (Rat.castHom ℝ) Complex.ofRealHom (normSqPolynomial K.pole K.polynomial)
      ((K.pole : ℝ) ^ 2 + t ^ 2)
  have hh : Complex.ofRealHom.comp (Rat.castHom ℝ) = Rat.castHom ℂ := by
    ext x
    exact Complex.ofReal_ratCast x
  rw [hh] at hc
  exact hc.symm

/-- At the real point `1/2`, the continued mass is the rational pole term. -/
public theorem high_gaussian_mass_extension_half (K : HighGaussianKernel) :
    K.massExtension (1 / 2) = (K.massPole : ℂ) := by
  unfold HighGaussianKernel.massExtension HighGaussianKernel.massPole
  simp only [Rat.cast_div, Rat.cast_mul, Rat.cast_pow, Rat.cast_sub, Rat.cast_one, Rat.cast_ofNat]
  congr 2
  have h :=
    eval_cast_map (RingHom.id ℚ) (Rat.castHom ℂ) (normSqPolynomial K.pole K.polynomial)
      (K.pole ^ 2 - (1 / 2) ^ 2)
  simp only [RingHom.comp_id, Rat.coe_castHom, Rat.cast_sub, Rat.cast_pow, Rat.cast_div,
    Rat.cast_one, Rat.cast_ofNat] at h
  exact h.symm

/-- In the strip between the two poles, the extended mass is a finite linear
combination of balanced opposite-pole products. -/
public theorem high_gaussian_mass_extension_sum (K : HighGaussianKernel) {z : ℂ}
    (hleft : -(K.pole : ℝ) < z.re) (hright : z.re < (K.pole : ℝ)) :
    K.massExtension z =
      ∑ j ∈ Finset.range (K.degree + 1),
        (K.normalization : ℂ) * ((normSqPolynomial K.pole K.polynomial).coeff j : ℂ) /
          (((K.pole : ℂ) + z) ^ (K.degree + 2 - j) * ((K.pole : ℂ) - z) ^ (K.degree + 2 - j)) := by
  have ha : 1 ≤ K.degree := by cases K <;> decide
  have hd := norm_sq_polynomial_degree K.pole K.polynomial ha (high_gaussian_polynomial_degree K)
  have hp : (K.pole : ℂ) + z ≠ 0 := by
    intro he
    have h := congrArg Complex.re he
    simp only [Complex.add_re, Complex.zero_re, ← Complex.ofReal_ratCast, Complex.ofReal_re] at h
    linarith only [h, hleft]
  have hm : (K.pole : ℂ) - z ≠ 0 := by
    intro he
    have h := congrArg Complex.re he
    simp only [Complex.sub_re, Complex.zero_re, ← Complex.ofReal_ratCast, Complex.ofReal_re] at h
    exact hright.ne (sub_eq_zero.mp h).symm
  let u := (K.pole : ℂ) ^ 2 - z ^ 2
  have he : u = ((K.pole : ℂ) + z) * ((K.pole : ℂ) - z) := by
    dsimp only [u]; ring
  have hu : u ≠ 0 := he ▸ mul_ne_zero hp hm
  unfold HighGaussianKernel.massExtension
  change
    (K.normalization : ℂ) * (normSqPolynomial K.pole K.polynomial).eval₂ (Rat.castHom ℂ) u /
        u ^ (K.degree + 2) =
      _
  rw [Polynomial.eval₂_eq_sum_range' _ (Nat.lt_succ_of_le hd)]
  simp only [Rat.coe_castHom, Finset.mul_sum, Finset.sum_div, ← mul_pow, ← he]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j ≤ K.degree + 2 :=
    (Nat.le_of_lt_succ (Finset.mem_range.mp hj)).trans (Nat.le_add_right _ _)
  have hpow : u ^ j / u ^ (K.degree + 2) = 1 / u ^ (K.degree + 2 - j) := by
    apply (div_eq_div_iff (pow_ne_zero _ hu) (pow_ne_zero _ hu)).mpr
    rw [← pow_add, Nat.add_comm j, Nat.sub_add_cancel hj', one_mul]
  rw [← mul_assoc, mul_div_assoc, hpow, mul_one_div]

end PseudoPrime.PrimeTestBounds.MillerRabin
