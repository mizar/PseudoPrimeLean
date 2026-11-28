/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleScalarResidual
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK141LowerCharge
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK156LowerCharge

/-! # Signs of the middle half-point residues -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- At the half point the mass extension is a rational product of two compact
numerator evaluations divided by the power of the balanced pole factor. -/
public theorem middle_half_point_re (Q : Polynomial ℚ) (a : ℚ) (m : ℕ) :
    (middleMassExtension Q a m ((1 / 2 : ℝ) : ℂ)).re =
      ((Q.eval (a + 1 / 2) * Q.eval (a - 1 / 2) / (a ^ 2 - (1 / 2 : ℚ) ^ 2) ^ m : ℚ) : ℝ) := by
  have hz : ((1 / 2 : ℝ) : ℂ) = ((1 / 2 : ℚ) : ℂ) := by
    simp only [Complex.ofReal_div, Complex.ofReal_one, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat,
      Complex.ofReal_ofNat]
  rw [hz, middle_mass_extension_product]
  rw [← Rat.cast_add, ← Rat.cast_neg, ← Rat.cast_add]
  have he (v : ℚ) : Q.eval₂ (Rat.castHom ℂ) (v : ℂ) = ((Q.eval v : ℚ) : ℂ) :=
    Polynomial.eval₂_at_apply (p := Q) (Rat.castHom ℂ) v
  rw [he, he, ← Rat.cast_pow, ← Rat.cast_pow, ← Rat.cast_sub, ← Rat.cast_pow, ← Rat.cast_mul, ←
    Rat.cast_div, ← Complex.ofReal_ratCast, Complex.ofReal_re]
  rw [add_comm (1 / 2 : ℚ), neg_add_eq_sub]

/-- A rational lower bound for six times the normalized K141 half-point
residue, used with its negative sign in the upper zero-mass bound. -/
public theorem middle_k141_half_point_lower :
    (24469 : ℝ) / 1000 ≤
      6 * (middleK141Norm : ℝ) *
        (middleMassExtension middleK141Kernel 2 16 ((1 / 2 : ℝ) : ℂ)).re := by
  rw [middle_half_point_re]
  have hc :
    (24469 : ℚ) / 1000 ≤
      6 * middleK141Norm *
        (middleK141Kernel.eval (2 + 1 / 2) * middleK141Kernel.eval (2 - 1 / 2) /
          (2 ^ 2 - (1 / 2 : ℚ) ^ 2) ^ 16) := by
    unfold middleK141Kernel
    rw [show (2 : ℚ) + 1 / 2 = (5 : ℤ) / (2 : ℤ) by decide +kernel,
      show (2 : ℚ) - 1 / 2 = (3 : ℤ) / (2 : ℤ) by decide +kernel,
      MiddleIntRow.eval_eq_shift_head _ 14 5 2 (by decide) (by decide),
      MiddleIntRow.eval_eq_shift_head _ 14 3 2 (by decide) (by decide)]
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_mul] using (Rat.cast_le (K := ℝ)).mpr hc

/-- A rational lower bound for six times the normalized K156 half-point
residue, used with its negative sign in the upper zero-mass bound. -/
public theorem middle_k156_half_point_lower :
    (45174 : ℝ) / 1000 ≤
      6 * (middleK156Norm : ℝ) *
        (middleMassExtension middleK156Kernel (49 / 20) 26 ((1 / 2 : ℝ) : ℂ)).re := by
  rw [middle_half_point_re]
  have hc :
    (45174 : ℚ) / 1000 ≤
      6 * middleK156Norm *
        (middleK156Kernel.eval ((49 / 20) + 1 / 2) * middleK156Kernel.eval ((49 / 20) - 1 / 2) /
          ((49 / 20) ^ 2 - (1 / 2 : ℚ) ^ 2) ^ 26) := by
    unfold middleK156Kernel
    rw [show (49 / 20 : ℚ) + 1 / 2 = (59 : ℤ) / (20 : ℤ) by decide +kernel,
      show (49 / 20 : ℚ) - 1 / 2 = (39 : ℤ) / (20 : ℤ) by decide +kernel,
      MiddleIntRow.eval_eq_shift_head _ 24 59 20 (by decide) (by decide),
      MiddleIntRow.eval_eq_shift_head _ 24 39 20 (by decide) (by decide)]
    decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_mul] using (Rat.cast_le (K := ℝ)).mpr hc

/-- Passage at the direct K141 cutoff gives a residual upper bound with
the fixed half-point budget and the normalized Euler tail allowance. -/
public theorem middle_k141_residual_ceiling
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n p q r : ℕ} [NeZero p]
    [NeZero q] [NeZero r] [NeZero n] [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)]
    [Fact (2 < q)] [Fact (2 < r)] (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hprod : n = p * q * r) (hp : Odd p) (hq : Odd q) (hrOdd : Odd r)
    (hL : Real.log n ∈ Set.Icc (42410 : ℝ) 400000)
    (hpass :
      ∀ l : ℕ,
        l.Prime →
          (l : ℝ) ≤ (gaussianDirectScale * Real.log n) ^ 2 →
          PrimeTest.StrongMillerRabinPass n (l : ZMod n)) :
    let x := Real.log ((gaussianDirectScale * Real.log n) ^ 2)
    let a : ℝ := 2
    let b : ℝ := 7 / 2
    let z := x + b
    let κ := (middleK141Norm : ℝ)
    let B := middleK141Profile.map (Rat.castHom ℝ)
    let M := (middleMomentPoly middleK141Profile (5 / 2) 0).map (Rat.castHom ℝ)
    let P := middleLowerEndpointPoly B M (a - 1 / 2)
    let E := middleEulerDecay B P κ a b (middleK141Scale : ℝ)
    ((7215924929 / 10 ^ 10) - 3 / 8 / gaussianDirectScale) * Real.exp (x / 2) -
            (61 / 1000) / 4 * x ^ 2 +
          Real.exp (-a * x) * E.eval x -
        Real.exp (-(a - 1 / 2) * x) *
          ((2 * κ * Real.exp (-a * b) / gaussianDirectScale) * B.eval z) ≤
      -(118 / 5) := by
  intro x a b z κ B M P E
  have h := middle_k141_direct_residual_of_pass hGRH hn ho hu hprod hp hq hrOdd hL hpass
  have hpole := middle_k141_half_point_lower
  have hk : (0 : ℝ) ≤ middleK141Norm := Rat.cast_nonneg.mpr (by decide +kernel)
  have h₁ :
    0 ≤
      (middleK141Norm : ℝ) *
        (Real.exp (-(1 / 2) * z) * (middleK141Kernel.eval₂ (Rat.castHom ℝ) (a - 1 / 2)) ^ 2 /
          (a - 1 / 2) ^ 32) :=
    mul_nonneg hk
      (div_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))
        (pow_nonneg (by norm_num only [a]) _))
  have h₂ :
    0 ≤
      (middleK141Norm : ℝ) *
        (Real.exp (-(5 / 2) * z) * (middleK141Kernel.eval₂ (Rat.castHom ℝ) (-(1 / 2))) ^ 2 /
          (-(1 / 2) : ℝ) ^ 32) :=
    mul_nonneg hk (div_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _)) (by norm_num only))
  dsimp only [x, a, b, z, κ, B, M, P, E] at h₁ h₂ ⊢
  dsimp only at h
  nlinarith only [h, hpole, h₁, h₂]

/-- Passage at the direct K156 cutoff gives a residual upper bound with
the fixed half-point budget and the normalized Euler tail allowance. -/
public theorem middle_k156_residual_ceiling
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n p q r : ℕ} [NeZero p]
    [NeZero q] [NeZero r] [NeZero n] [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)]
    [Fact (2 < q)] [Fact (2 < r)] (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hprod : n = p * q * r) (hp : Odd p) (hq : Odd q) (hrOdd : Odd r)
    (hL : Real.log n ∈ Set.Icc (400000 : ℝ) 7000000)
    (hpass :
      ∀ l : ℕ,
        l.Prime →
          (l : ℝ) ≤ (gaussianDirectScale * Real.log n) ^ 2 →
          PrimeTest.StrongMillerRabinPass n (l : ZMod n)) :
    let x := Real.log ((gaussianDirectScale * Real.log n) ^ 2)
    let a : ℝ := 49 / 20
    let b : ℝ := 7 / 2
    let z := x + b
    let κ := (middleK156Norm : ℝ)
    let B := middleK156Profile.map (Rat.castHom ℝ)
    let M := (middleMomentPoly middleK156Profile (59 / 20) 0).map (Rat.castHom ℝ)
    let P := middleLowerEndpointPoly B M (a - 1 / 2)
    let E := middleEulerDecay B P κ a b (middleK156Scale : ℝ)
    ((721603265 / 10 ^ 9) - 3 / 8 / gaussianDirectScale) * Real.exp (x / 2) -
            (61 / 1000) / 4 * x ^ 2 +
          Real.exp (-a * x) * E.eval x -
        Real.exp (-(a - 1 / 2) * x) *
          ((2 * κ * Real.exp (-a * b) / gaussianDirectScale) * B.eval z) ≤
      if 29 ≤ x then -(901 / 20) else -(4407 / 100) := by
  intro x a b z κ B M P E
  have h := middle_k156_direct_residual_of_pass hGRH hn ho hu hprod hp hq hrOdd hL hpass
  have hpole := middle_k156_half_point_lower
  have hk : (0 : ℝ) ≤ middleK156Norm := Rat.cast_nonneg.mpr (by decide +kernel)
  have h₁ :
    0 ≤
      (middleK156Norm : ℝ) *
        (Real.exp (-(1 / 2) * z) * (middleK156Kernel.eval₂ (Rat.castHom ℝ) (a - 1 / 2)) ^ 2 /
          (a - 1 / 2) ^ 52) :=
    mul_nonneg hk
      (div_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))
        (pow_nonneg (by norm_num only [a]) _))
  dsimp only [x, a, b, z, κ, B, M, P, E] at h₁ ⊢
  dsimp only at h
  by_cases hh : 29 ≤ x
  · simp only [x, hh, ite_true] at h ⊢
    nlinarith only [h, hpole, h₁]
  · simp only [x, hh, ite_false] at h ⊢
    nlinarith only [h, hpole, h₁]

end PseudoPrime.PrimeTestBounds.MillerRabin
