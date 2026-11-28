/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleMassKernel
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighMassPole
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131Kernel
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighMassMellin
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131Kernel

/-! # Balanced opposite-pole decomposition of the middle mass kernel -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Extend the rational critical-line mass to the strip between the two poles.
The normalization is applied separately when comparing the zero masses. -/
public noncomputable def middleMassExtension (Q : Polynomial ℚ) (a : ℚ) (m : ℕ) (z : ℂ) : ℂ :=
  let u := (a : ℂ) ^ 2 - z ^ 2
  (normSqPolynomial a Q).eval₂ (Rat.castHom ℂ) u / u ^ m

/-- The middle mass extension is even. -/
public theorem middle_mass_extension_even (Q : Polynomial ℚ) (a : ℚ) (m : ℕ) (z : ℂ) :
    middleMassExtension Q a m (-z) = middleMassExtension Q a m z := by
  simp only [middleMassExtension, neg_sq]

/-- Factor the continued numerator into the two reflected evaluations of
the compact polynomial. At the half-point this is the principal pole product. -/
public theorem middle_mass_extension_product (Q : Polynomial ℚ) (a : ℚ) (m : ℕ) (z : ℂ) :
    middleMassExtension Q a m z =
      Q.eval₂ (Rat.castHom ℂ) (z + a) * Q.eval₂ (Rat.castHom ℂ) (-z + a) /
        (((a : ℂ) ^ 2 - z ^ 2) ^ m) := by
  have h := norm_sq_polynomial_reflect (Rat.castHom ℂ) a Q z
  simpa only [middleMassExtension, Rat.coe_castHom] using
    congrArg (fun v : ℂ ↦ v / (((a : ℂ) ^ 2 - z ^ 2) ^ m)) h

/-- Restriction of the extension to the critical line recovers the real rational weight. -/
public theorem middle_mass_extension_line (Q : Polynomial ℚ) (a : ℚ) (m : ℕ) (t : ℝ) :
    middleMassExtension Q a m (Complex.I * (t : ℂ)) =
      (((normSqPolynomial a Q).eval₂ (Rat.castHom ℝ) ((a : ℝ) ^ 2 + t ^ 2) /
            ((a : ℝ) ^ 2 + t ^ 2) ^ m :
          ℝ) :
        ℂ) := by
  have hu : (a : ℂ) ^ 2 - (Complex.I * (t : ℂ)) ^ 2 = (((a : ℝ) ^ 2 + t ^ 2 : ℝ) : ℂ) := by
    simp only [mul_pow, Complex.I_sq, neg_one_mul, sub_neg_eq_add, Complex.ofReal_add,
      Complex.ofReal_pow, Complex.ofReal_ratCast]
  simp only [middleMassExtension, hu, Complex.ofReal_div, Complex.ofReal_pow]
  congr 1
  simp only [Polynomial.eval₂_eq_sum_range, Complex.ofReal_sum, Complex.ofReal_mul,
    Complex.ofReal_pow, Rat.coe_castHom, Complex.ofReal_ratCast]

/-- Expand the middle mass into balanced opposite-pole products without
performing coefficient-specific partial fraction calculations. -/
public theorem middle_mass_extension_sum (Q : Polynomial ℚ) (a : ℚ) {d : ℕ} (hd₀ : 1 ≤ d)
    (hQ : Q.natDegree ≤ d) {z : ℂ} (hleft : -(a : ℝ) < z.re) (hright : z.re < (a : ℝ)) :
    middleMassExtension Q a (d + 2) z =
      ∑ j ∈ Finset.range (d + 1),
        ((normSqPolynomial a Q).coeff j : ℂ) /
          (((a : ℂ) + z) ^ (d + 2 - j) * ((a : ℂ) - z) ^ (d + 2 - j)) := by
  have hd := norm_sq_polynomial_degree a Q hd₀ hQ
  have hp : (a : ℂ) + z ≠ 0 := by
    intro he
    have h := congrArg Complex.re he
    simp only [Complex.add_re, Complex.zero_re, ← Complex.ofReal_ratCast, Complex.ofReal_re] at h
    linarith only [h, hleft]
  have hm : (a : ℂ) - z ≠ 0 := by
    intro he
    have h := congrArg Complex.re he
    simp only [Complex.sub_re, Complex.zero_re, ← Complex.ofReal_ratCast, Complex.ofReal_re] at h
    exact hright.ne (sub_eq_zero.mp h).symm
  let u := (a : ℂ) ^ 2 - z ^ 2
  have he : u = ((a : ℂ) + z) * ((a : ℂ) - z) := by
    dsimp only [u]; ring
  have hu : u ≠ 0 := he ▸ mul_ne_zero hp hm
  unfold middleMassExtension
  change (normSqPolynomial a Q).eval₂ (Rat.castHom ℂ) u / u ^ (d + 2) = _
  rw [Polynomial.eval₂_eq_sum_range' _ (Nat.lt_succ_of_le hd)]
  simp only [Rat.coe_castHom, Finset.sum_div, ← mul_pow, ← he]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j ≤ d + 2 := (Nat.le_of_lt_succ (Finset.mem_range.mp hj)).trans (Nat.le_add_right _ _)
  have hpow : u ^ j / u ^ (d + 2) = 1 / u ^ (d + 2 - j) := by
    apply (div_eq_div_iff (pow_ne_zero _ hu) (pow_ne_zero _ hu)).mpr
    rw [← pow_add, Nat.add_comm j, Nat.sub_add_cancel hj', one_mul]
  rw [mul_div_assoc, hpow, mul_one_div]

/-- The signed Mellin profile corresponding to the unnormalized middle mass.
Each symmetric profile counts the equal opposite-pole factors twice. -/
public noncomputable def middleMassProfile (Q : Polynomial ℚ) (a : ℚ) (d : ℕ) (u : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (d + 1),
    ((normSqPolynomial a Q).coeff j : ℝ) / 2 * k131SymmetricProfile a (d + 2 - j) (d + 2 - j) u

/-- The balanced profile has the mass extension as its Mellin transform on the open strip. -/
public theorem middle_mass_hasMellin (Q : Polynomial ℚ) (a : ℚ) {d : ℕ} (hd : 1 ≤ d)
    (hQ : Q.natDegree ≤ d) {z : ℂ} (hl : -(a : ℝ) < z.re) (hr : z.re < (a : ℝ)) :
    HasMellin (fun u ↦ (middleMassProfile Q a d u : ℂ)) z (middleMassExtension Q a (d + 2) z) := by
  rw [middle_mass_extension_sum Q a hd hQ hl hr]
  unfold middleMassProfile
  simp only [Complex.ofReal_sum]
  apply k131_mellin_finsum
  intro j hj
  have hj' := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hm := Nat.sub_pos_of_lt (hj'.trans_lt (Nat.lt_add_of_pos_right (by decide : 0 < 2)))
  simpa only [Complex.ofReal_ratCast] using
    balanced_mellin hl hr (d + 2 - j) hm ((normSqPolynomial a Q).coeff j : ℝ)

/-- The signed zero score is bounded by the real part of the middle mass extension
on the critical line, with each zero counted according to its divisor. -/
public theorem middle_signed_zero_le_extension (Q : Polynomial ℚ) {m : ℕ}
    (hQ : 2 * Q.natDegree + 3 ≤ 2 * m - 1) {a : ℚ} (ha : 1 / 2 < (a : ℝ)) (b : ℝ) {q : ℕ} [NeZero q]
    (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {X κ : ℝ} (hX : 0 < X) (hκ : 0 ≤ κ) :
    let K := fun i : ℕ ↦ LLS.PaperStatements.shiftedPoleKernel (max 1 i) a b (le_max_left _ _) ha
    let D := MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ
    (-((κ : ℂ) *
            (∑' ρ : ℂ,
              ∑ i ∈ Finset.Ico 3 (2 * m),
                ((Q ^ 2).coeff (2 * m - 1 - i) : ℂ) * (K i).oscillatingZeroTerm χ X ρ)).re) ≤
      κ * (∑' ρ : ℂ, (D ρ : ℝ) * (middleMassExtension Q a m (Complex.I * ρ.im)).re) := by
  simp only [middle_mass_extension_line, Complex.ofReal_re]
  exact middle_signed_zero_le_mass Q hQ ha b hq hGRH hp hne hinv hX hκ

end PseudoPrime.PrimeTestBounds.MillerRabin
