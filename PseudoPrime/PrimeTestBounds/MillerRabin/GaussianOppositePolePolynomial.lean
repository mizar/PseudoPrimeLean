/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianOppositePoleFourier

/-! # Polynomial factors of opposite-pole Fourier integrals -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Polynomial factor of the mixed-pole Fourier integral for nonnegative
angular frequency, after removing `π exp(-a*x)`. -/
public noncomputable def oppositePolePolynomial (a : ℚ) (p q : ℕ) : Polynomial ℚ :=
  match p, q with
  | 0, _ => 0
  | n + 1, 0 => Polynomial.C (2 / (n.factorial : ℚ)) * Polynomial.X ^ n
  | 1, 1 => Polynomial.C (1 / a)
  | p + 1, q + 1 =>
    Polynomial.C (1 / (2 * a)) *
      (oppositePolePolynomial a p (q + 1) + oppositePolePolynomial a (p + 1) q)
termination_by p + q
decreasing_by
  · exact Nat.add_lt_add_right (Nat.lt_succ_self _) _
  · exact Nat.add_lt_add_left (Nat.lt_succ_self _) _

/-- The positive pole's inverse profile simplifies to an exponential times its log monomial. -/
private theorem pole_profile_nonneg_argument (a x : ℝ) (hx : 0 ≤ x) (n : ℕ) :
    Analysis.shiftedPoleProfile n a 0 (Real.exp (-x)) =
      Real.exp (-a * x) * x ^ n / n.factorial := by
  have hx' : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx)
  simp only [Analysis.shiftedPoleProfile, neg_zero, Real.exp_zero, mul_one, min_eq_left hx',
    Real.log_exp, neg_neg, Real.rpow_def_of_pos (Real.exp_pos (-x))]
  rw [show -x * a = -a * x by ring]

/-- Above total order one, the mixed-pole Fourier integral is exactly
the normalized polynomial times the common exponential at nonnegative frequency. -/
public theorem opposite_pole_fourier_polynomial (a : ℚ) (ha : 1 ≤ (a : ℝ)) {x : ℝ} (hx : 0 ≤ x)
    (p q : ℕ) (hpq : 2 ≤ p + q) :
    (∫ t : ℝ, oppositePoleMode a x p q t) =
      ((Real.pi * Real.exp (-(a : ℝ) * x) * (oppositePolePolynomial a p q).eval₂ (Rat.castHom ℝ) x :
          ℝ) :
        ℂ) := by
  have ha' := zero_lt_one.trans_le ha
  induction p, q using oppositePolePolynomial.induct with
  | case1 q =>
    cases q with
    | zero => exact (by decide : ¬2 ≤ 0 + 0) hpq |>.elim
    | succ
      n =>
      have hn : 1 ≤ n := Nat.le_of_succ_le_succ (by simpa only [Nat.zero_add] using hpq)
      have hsupport : Real.exp 0 ≤ Real.exp (-(-x)) :=
        Real.exp_le_exp.mpr (by simpa only [neg_neg] using hx)
      rw [opposite_pole_fourier_reflect, opposite_pole_fourier_positive ha' _ hn,
        Analysis.shiftedPoleProfile_support hn _ hsupport]
      simp only [oppositePolePolynomial, Polynomial.eval₂_zero, Complex.ofReal_zero, mul_zero]
  | case2
    n =>
    have hn : 1 ≤ n := Nat.le_of_succ_le_succ (by simpa only [Nat.add_zero] using hpq)
    rw [opposite_pole_fourier_positive ha' _ hn, pole_profile_nonneg_argument _ _ hx]
    simp only [oppositePolePolynomial, Polynomial.eval₂_mul, Polynomial.eval₂_C,
      Polynomial.eval₂_pow, Polynomial.eval₂_X, Rat.coe_castHom, Rat.cast_div, Rat.cast_ofNat,
      Rat.cast_natCast, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_pow,
      Complex.ofReal_natCast, Complex.ofReal_ofNat]
    simp only [div_eq_mul_inv]
    ring
  | case3 =>
    rw [opposite_pole_fourier_base ha', abs_of_nonneg hx]
    simp only [oppositePolePolynomial, Polynomial.eval₂_C, Rat.coe_castHom, Rat.cast_div,
      Rat.cast_one, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_one]
    simp only [div_eq_mul_inv]
    ring
  | case4 p q hne ih₁
    ih₂ =>
    have hpq' : 1 ≤ p + q :=
      Nat.one_le_iff_ne_zero.mpr fun h ↦
        hne (Nat.add_eq_zero_iff.mp h).1 (Nat.add_eq_zero_iff.mp h).2
    have hp : 2 ≤ p + (q + 1) := by
      rw [← Nat.add_assoc]
      exact Nat.add_le_add_right hpq' 1
    have hq : 2 ≤ (p + 1) + q := by
      rw [Nat.add_right_comm]
      exact Nat.add_le_add_right hpq' 1
    rw [opposite_pole_fourier_step ha x p q hpq', ih₁ hp, ih₂ hq,
      oppositePolePolynomial.eq_4 a p q hne]
    simp only [Polynomial.eval₂_mul, Polynomial.eval₂_add, Polynomial.eval₂_C, Rat.coe_castHom,
      Rat.cast_div, Rat.cast_mul, Rat.cast_one, Rat.cast_ofNat, Complex.ofReal_mul,
      Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat,
      Complex.ofReal_ratCast]
    simp only [div_eq_mul_inv]
    ring

/-- The balanced opposite-pole polynomial evaluates the Fourier integral at
the absolute frequency, by reflecting a negative frequency. -/
public theorem cauchy_fourier_polynomial (a : ℚ) (ha : 1 ≤ (a : ℝ)) (m : ℕ) (hm : 1 ≤ m) (x : ℝ) :
    (∫ t : ℝ, Complex.exp ((x * t : ℝ) * Complex.I) / (((((a : ℝ) ^ 2 + t ^ 2 : ℝ) : ℂ)) ^ m)) =
      ((Real.pi * Real.exp (-(a : ℝ) * |x|) *
            (oppositePolePolynomial a m m).eval₂ (Rat.castHom ℝ) |x| :
          ℝ) :
        ℂ) := by
  have hsum : 2 ≤ m + m := Nat.add_le_add hm hm
  rw [cauchy_fourier_eq_opposite]
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx, opposite_pole_fourier_polynomial a ha hx m m hsum]
  · rw [abs_of_nonpos hx, opposite_pole_fourier_reflect,
      opposite_pole_fourier_polynomial a ha (neg_nonneg.mpr hx) m m hsum]

end PseudoPrime.PrimeTestBounds.MillerRabin
