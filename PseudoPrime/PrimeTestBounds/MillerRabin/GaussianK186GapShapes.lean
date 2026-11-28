/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186FiniteGap

import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186FiniteGap
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186EulerTail
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186FiniteEnvelope
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186ReflectedBudget

/-! # Rational shapes of the two finite exponential-polynomial costs -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Cast a rational unshifted Laplace moment without expanding its coefficients. -/
private theorem k186_map_moment (P : Polynomial ℚ) (s : ℚ) :
    (middleMomentPoly P s 0).map (Rat.castHom ℝ) =
      middleMomentPoly (P.map (Rat.castHom ℝ)) (s : ℝ) 0 := by
  have hd := Polynomial.natDegree_map_eq_of_injective (Rat.castHom ℝ).injective (p := P)
  simp only [middleMomentPoly, Polynomial.map_comp, Polynomial.map_sum, Polynomial.map_add,
    Polynomial.map_X, Polynomial.map_C, Polynomial.map_mul, Rat.coe_castHom,
    ← Polynomial.hasseDeriv_map, hd, Rat.cast_div, Rat.cast_natCast, Rat.cast_zero, Rat.cast_pow]

/-- Both representations use the same unshifted Laplace polynomial. -/
private theorem k186_euler_moment_eq (P : Polynomial ℝ) (s : ℝ) :
    eulerMomentPoly P s = middleMomentPoly P s 0 := by
  simp only [eulerMomentPoly, middleMomentPoly, Polynomial.C_0, add_zero, Polynomial.comp_X]

/-- The rational profile translated to the physical origin of the finite comparison. -/
noncomputable def k186GapProfileRat : Polynomial ℚ :=
  HighGaussianKernel.k186.ratProfile.comp (Polynomial.X + Polynomial.C 5)

/-- The first right Euler term, including its multiplier in the finite margin. -/
noncomputable def k186GapEulerNineRat : Polynomial ℚ :=
  Polynomial.C 4 * middleMomentPoly (highGaussianMassPolynomial .k186) (9 / 4) 0

/-- The second right Euler term, including its multiplier in the finite margin. -/
noncomputable def k186GapEulerElevenRat : Polynomial ℚ :=
  let q := highGaussianMassPolynomial .k186
  let Q := Polynomial.X ^ 2 * (Polynomial.C (13 / 4) * q - q.derivative)
  Polynomial.C (1 / 6) * (Polynomial.X ^ 2 * q + middleMomentPoly Q (11 / 4) 0)

/-- The signed reflected and forward endpoint moments, translated once. -/
noncomputable def k186GapEndpointRat : Polynomial ℚ :=
  let B := HighGaussianKernel.k186.ratProfile
  (Polynomial.C 6 *
          (Polynomial.C (13 / 4) * middleMomentPoly B (9 / 4) 0 +
            middleMomentPoly B.derivative (9 / 4) 0) +
        Polynomial.C 3 * middleMomentPoly B (13 / 4) 0).comp
    (Polynomial.X + Polynomial.C 5)

/-- Only one fixed exponential multiplies the rational profile in the first cost. -/
theorem k186_gap_nine_rat :
    k186GapRateNine =
      Polynomial.C (Real.exp (-55 / 4) * (2 / gaussianK186FarScale)) *
          k186GapProfileRat.map (Rat.castHom ℝ) +
        k186GapEulerNineRat.map (Rat.castHom ℝ) := by
  simp only [k186GapRateNine, k186GapProfileRat, k186GapEulerNineRat, Polynomial.map_comp,
    Polynomial.map_add, Polynomial.map_mul, Polynomial.map_X, Polynomial.map_C, Rat.coe_castHom,
    Rat.cast_ofNat, Rat.cast_div, high_comp_profile_map, k186_map_moment, k186MassPoly,
    k186_euler_moment_eq]

/-- The endpoint and right Euler polynomials in the second cost have
fixed rational shapes. Only two scalar factors need real enclosures. -/
theorem k186_gap_eleven_rat :
    k186GapRateEleven =
      Polynomial.C (Real.exp (-55 / 4)) *
          (k186GapEndpointRat.map (Rat.castHom ℝ) +
            Polynomial.C (3 * Real.log (2 * Real.pi) - 7) * k186GapProfileRat.map (Rat.castHom ℝ)) +
        k186GapEulerElevenRat.map (Rat.castHom ℝ) := by
  simp only [k186GapRateEleven, k186GapProfileRat, k186GapEndpointRat, k186GapEulerElevenRat,
    k186EulerLatePoly, k186ReflectedMoment, Polynomial.map_comp, Polynomial.map_add,
    Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
    ← Polynomial.derivative_map, Rat.coe_castHom, Rat.cast_ofNat, Rat.cast_one, Rat.cast_div,
    high_comp_profile_map, k186_map_moment, k186MassPoly, k186_euler_moment_eq, Polynomial.add_comp,
    Polynomial.mul_comp, Polynomial.C_comp]
  ring

/-- Twice differentiate a weighted rational polynomial, retaining the
polynomial factor for exact coefficient checks. -/
noncomputable def k186RatCurv (r : ℚ) (P : Polynomial ℚ) : Polynomial ℚ :=
  P.derivative.derivative - Polynomial.C (2 * r) * P.derivative + Polynomial.C (r ^ 2) * P

/-- The fixed rational curvature polynomial casts to the analytic one. -/
theorem k186_rat_curv_map (r : ℚ) (P : Polynomial ℚ) :
    (k186RatCurv r P).map (Rat.castHom ℝ) =
      gaussianDecayDeriv (r : ℝ) (gaussianDecayDeriv (r : ℝ) (P.map (Rat.castHom ℝ))) := by
  rw [gaussian_decay_deriv_twice]
  simp only [k186RatCurv, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_C, ← Polynomial.derivative_map, Rat.coe_castHom, Rat.cast_mul, Rat.cast_pow,
    Rat.cast_ofNat]

/-- A signed lower bound on a polynomial gives an upper bound on its
negative weighted contribution. The exponential is bounded only on its positive part. -/
private theorem neg_weighted_le {r a x p m : ℝ} (hr : 0 ≤ r) (hx : a ≤ x) (hm : m ≤ p) :
    -(Real.exp (-r * x) * p) ≤ Real.exp (-r * a) * max 0 (-m) := by
  rw [← mul_neg]
  refine
    (mul_le_mul_of_nonneg_left ((neg_le_neg hm).trans (le_max_right (0 : ℝ) (-m)))
          (Real.exp_nonneg _)).trans
      ?_
  exact
    mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hx (neg_nonpos.mpr hr))) (le_max_left _ _)

/-- For the K186 curvature only the two signed decay polynomials
and the positive central slope need upper bounds. -/
theorem k186_gap_curv_le_of_polys {a b x m₁ m₂ : ℝ} (hx : x ∈ Set.Icc a b)
    (h₁ : m₁ ≤ (gaussianDecayDeriv (9 / 4) (gaussianDecayDeriv (9 / 4) k186GapRateNine)).eval x)
    (h₂ :
      m₂ ≤ (gaussianDecayDeriv (11 / 4) (gaussianDecayDeriv (11 / 4) k186GapRateEleven)).eval x) :
    gaussianMidResidualCurv k186GapSlope (4 * (301 / 20000 + 1 / 6000)) k186GapRates k186GapProfiles
        x ≤
      k186GapSlope / 4 * Real.exp (b / 2) + Real.exp (-(9 / 4 : ℝ) * a) * max 0 (-m₁) +
        Real.exp (-(11 / 4 : ℝ) * a) * max 0 (-m₂) := by
  have hs : 0 ≤ k186GapSlope / 4 := by norm_num only [k186GapSlope, gaussianK186FarScale]
  have hE :=
    mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hx.2 (by norm_num only : (0 : ℝ) ≤ 2))) hs
  have hb₁ := neg_weighted_le (by norm_num only : (0 : ℝ) ≤ 9 / 4) hx.1 h₁
  have hb₂ := neg_weighted_le (by norm_num only : (0 : ℝ) ≤ 11 / 4) hx.1 h₂
  have hP :
    0 ≤ Real.exp (-(1 / 2 : ℝ) * x) * ((1 / 2 : ℝ) ^ 2 * (78548 * Real.exp (-(5 / 2)))) := by
    positivity
  simp only [gaussianMidResidualCurv, gaussianDecaySum, k186GapRates, k186GapProfiles,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]
  simp only [gaussian_decay_deriv_twice, Polynomial.derivative_C, Polynomial.derivative_C_mul,
    Polynomial.derivative_X, Polynomial.derivative_zero, Polynomial.derivative_one, mul_zero,
    sub_zero, Polynomial.C_0, zero_mul, add_zero, zero_pow (by decide : 2 ≠ 0), Polynomial.eval_C,
    Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_zero, Polynomial.eval_sub, neg_zero,
    Real.exp_zero] at hb₁ hb₂ ⊢
  linarith only [hE, hb₁, hb₂, hP]

/-- Compare an endpoint using three scalar upper bounds for the costs
and a lower enclosure for the positive exponential. -/
theorem k186_gap_endpoint_of_bounds {x E U₁ U₂ U₃ lower : ℝ} (he : E ≤ Real.exp (x / 2))
    (h₁ : Real.exp (-(9 / 4 : ℝ) * x) * k186GapRateNine.eval x ≤ U₁)
    (h₂ : Real.exp (-(11 / 4 : ℝ) * x) * k186GapRateEleven.eval x ≤ U₂)
    (h₃ : Real.exp (-(x + 5) / 2) * 78548 ≤ U₃)
    (h :
      lower ≤
        k186GapSlope * E + (94173 / 1250 - 3 / 100 - 3 / 16 - 6 / 5) - 301 / 20000 * x ^ 2 -
          (x + 5) ^ 2 / 6000 -
          U₁ -
          U₂ -
          U₃) :
    lower ≤ k186FiniteGap x := by
  have hs : 0 ≤ k186GapSlope := by norm_num only [k186GapSlope, gaussianK186FarScale]
  have hE := mul_le_mul_of_nonneg_left he hs
  rw [k186_finite_gap_grouped]
  change _ ≤ k186GapSlope * _ + _ - _ - _ - _ - _ - _
  linarith only [h, hE, h₁, h₂, h₃]

end PseudoPrime.PrimeTestBounds.MillerRabin
