/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleEndpointCheck
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleResidualProfile

/-! # Curvature transfer from integer rows to the global middle profiles -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- At unit width the row curvature is the second decay derivative. -/
private theorem local_curv_eq_decay (P : Polynomial ℝ) (r : ℝ) :
    gaussianLocalCurv P r 1 = gaussianDecayDeriv r (gaussianDecayDeriv r P) := by
  simp only [gaussianLocalCurv, gaussianDecayDeriv, one_pow, div_one, Polynomial.derivative_sub,
    Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul, zero_add, Polynomial.C_1, one_mul,
    Polynomial.C_mul, Polynomial.C_pow, Polynomial.C_ofNat]
  ring

/-- Translating the input commutes with applying one decay derivative. -/
private theorem decay_deriv_translate (P : Polynomial ℝ) (r o : ℝ) :
    gaussianDecayDeriv r (P.comp (Polynomial.X + Polynomial.C o)) =
      (gaussianDecayDeriv r P).comp (Polynomial.X + Polynomial.C o) := by
  simp only [gaussianDecayDeriv, Polynomial.sub_comp, Polynomial.mul_comp, Polynomial.C_comp,
    Polynomial.derivative_comp, Polynomial.derivative_add, Polynomial.derivative_X,
    Polynomial.derivative_C, add_zero, one_mul]

/-- A row representing a translated profile bounds the global second decay
derivative by one integer curvature cap at the right endpoint. -/
public theorem middle_row_curvature_le (A : MiddleIntRow) (N : ℕ) (rn rd p d : ℤ) (hA : 0 < A.den)
    (hrd : 0 < rd) (hp : 0 ≤ p) (hd : 0 < d) {P : Polynomial ℝ} {o t : ℝ} (ht : 0 ≤ t)
    (htu : t ≤ (p : ℝ) / d)
    (he : ∀ u : ℝ, ((A.poly N).map (Rat.castHom ℝ)).eval u = P.eval (u + o)) :
    |(gaussianDecayDeriv ((rn : ℝ) / rd) (gaussianDecayDeriv ((rn : ℝ) / rd) P)).eval (t + o)| ≤
      (A.curvCap N rn rd p d : ℝ) / A.den := by
  have hP : (A.poly N).map (Rat.castHom ℝ) = P.comp (Polynomial.X + Polynomial.C o) := by
    apply Polynomial.funext
    intro u
    simpa only [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_C] using he u
  have h := A.curv_cap_le N rn rd p d hA hrd hp hd ht htu
  rwa [hP, local_curv_eq_decay, decay_deriv_translate, decay_deriv_translate, Polynomial.eval_comp,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C] at h

/-- Rational upper bound for the absolute second decay derivative on a cell. -/
@[expose]
public def middleCurvUpper (A : MiddleIntRow) (N : ℕ) (rn rd u v : ℤ) : ℚ :=
  ((A.curvCap N rn rd u v : ℤ) : ℚ) / A.den

/-- A curvature cap and a grid value at the left endpoint bound the signed
curvature of one exponentially decaying profile. -/
public theorem middle_row_decay_curv_le (A : MiddleIntRow) (N : ℕ) (rn rd u v : ℤ) (j : ℕ)
    (hA : 0 < A.den) (hrn : 0 ≤ rn) (hrd : 0 < rd) (hu : 0 ≤ u) (hv : 0 < v) {P : Polynomial ℝ}
    {o t l : ℝ} (ht : 0 ≤ t) (htu : t ≤ (u : ℝ) / v) (hlo : l ≤ t + o)
    (hj : (j : ℝ) / 80 = ((rn : ℝ) / rd) * l) (hden : 0 < middleTailExpDen j)
    (he : ∀ w : ℝ, ((A.poly N).map (Rat.castHom ℝ)).eval w = P.eval (w + o)) :
    -(Real.exp (-((rn : ℝ) / rd) * (t + o)) *
          (gaussianDecayDeriv ((rn : ℝ) / rd) (gaussianDecayDeriv ((rn : ℝ) / rd) P)).eval
            (t + o)) ≤
      (middleCurvUpper A N rn rd u v / middleTailExpDen j : ℚ) := by
  have h := middle_row_curvature_le A N rn rd u v hA hrd hu hv ht htu he
  have he := middle_tail_exp_le j hden
  rw [hj, ← neg_mul, Rat.cast_div, Rat.cast_one] at he
  have hz :=
    (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonpos_left hlo
            (neg_nonpos.mpr
              (div_nonneg (Int.cast_nonneg_iff.mpr hrn) (Int.cast_nonneg_iff.mpr hrd.le))))).trans
      he
  rw [← mul_neg]
  refine (mul_le_mul_of_nonneg_left (neg_le_abs _) (Real.exp_pos _).le).trans ?_
  simp only [middleCurvUpper, Rat.cast_div, Rat.cast_intCast]
  simpa only [one_div, inv_mul_eq_div] using
    mul_le_mul hz h (abs_nonneg _) ((Real.exp_pos _).le.trans hz)

end PseudoPrime.PrimeTestBounds.MillerRabin
