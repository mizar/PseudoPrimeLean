/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighZeroUpper
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighMassTransform
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianOppositePolePolynomial
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighKernelData
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.Tactic.Linarith

/-! # Sign criterion for the high Gaussian Euler tail -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A rational polynomial whose translated coefficients are nonpositive
is nonpositive to the right of the translation point. -/
public theorem shifted_poly_eval_nonpos (P : Polynomial ℚ) (b : ℚ)
    (hc : ∀ j, (P.comp (Polynomial.X + Polynomial.C b)).coeff j ≤ 0) {x : ℝ} (hx : (b : ℝ) ≤ x) :
    P.eval₂ (Rat.castHom ℝ) x ≤ 0 := by
  let Q := P.comp (Polynomial.X + Polynomial.C b)
  have h : Q.eval₂ (Rat.castHom ℝ) (x - (b : ℝ)) = P.eval₂ (Rat.castHom ℝ) x := by
    unfold Q
    rw [Polynomial.eval₂_comp]
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_X, Polynomial.eval₂_C, Rat.coe_castHom,
      sub_add_cancel]
  rw [← h, Polynomial.eval₂_eq_sum_range]
  apply Finset.sum_nonpos
  intro j _
  have hq : ((Q.coeff j : ℚ) : ℝ) ≤ 0 := Rat.cast_nonpos.mpr (hc j)
  exact
    mul_nonpos_of_nonpos_of_nonneg (by simpa only [Rat.coe_castHom] using hq)
      (pow_nonneg (sub_nonneg.mpr hx) j)

/-- A pointwise nonpositive mass polynomial removes the high Euler tail from
the three-character zero upper bound. -/
public theorem high_gaussian_euler_tail_nonpos (K : HighGaussianKernel) {p q r : ℕ}
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) {X : ℝ}
    (hX : 0 < X)
    (hpoly : ∀ x : ℝ, Real.log X ≤ x → (highGaussianMassPolynomial K).eval₂ (Rat.castHom ℝ) x ≤ 0) :
    (∑' m : { m : ℕ // ⌊X⌋₊ < m },
        ArithmeticFunction.vonMangoldt m.val * (3 - ((a m.val).re + (b m.val).re + (c m.val).re)) *
          (m.val : ℝ) ^ (-(K.pole : ℝ) - 1 / 2) *
          (highGaussianMassPolynomial K).eval₂ (Rat.castHom ℝ) (Real.log m.val)) ≤
      0 := by
  apply tsum_nonpos
  intro m
  have hx : X < (m.val : ℝ) := (Nat.floor_lt hX.le).mp m.property
  have ha := (Complex.re_le_norm (a m.val)).trans (a.norm_le_one _)
  have hb := (Complex.re_le_norm (b m.val)).trans (b.norm_le_one _)
  have hc := (Complex.re_le_norm (c m.val)).trans (c.norm_le_one _)
  have hd : 0 ≤ 3 - ((a m.val).re + (b m.val).re + (c m.val).re) := by linarith only [ha, hb, hc]
  exact
    mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg hd)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (hpoly _ (Real.log_le_log hX hx.le))

/-- Given the translated coefficient certificate for K196, its Euler tail is
nonpositive on the manuscript's entire log-cutoff range. -/
public theorem high_k196_euler_tail_nonpos {p q r : ℕ} (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) {X : ℝ} (hX : 0 < X)
    (hlog : 75 / 2 ≤ Real.log X)
    (hc :
      ∀ j,
        ((highGaussianMassPolynomial .k196).comp (Polynomial.X + Polynomial.C (75 / 2))).coeff j ≤
          0) :
    (∑' m : { m : ℕ // ⌊X⌋₊ < m },
        ArithmeticFunction.vonMangoldt m.val * (3 - ((a m.val).re + (b m.val).re + (c m.val).re)) *
          (m.val : ℝ) ^ (-(HighGaussianKernel.k196.pole : ℝ) - 1 / 2) *
          (highGaussianMassPolynomial .k196).eval₂ (Rat.castHom ℝ) (Real.log m.val)) ≤
      0 := by
  apply high_gaussian_euler_tail_nonpos .k196 a b c hX
  intro x hx
  apply shifted_poly_eval_nonpos _ (75 / 2) hc
  simpa only [Rat.cast_div, Rat.cast_ofNat] using hlog.trans hx

/-- The mixed-pole Fourier polynomial has degree below its positive pole order. -/
private theorem opposite_poly_degree (a : ℚ) (p q : ℕ) :
    (oppositePolePolynomial a p q).natDegree ≤ p - 1 := by
  induction p, q using oppositePolePolynomial.induct with
  | case1 q => simp only [oppositePolePolynomial, Polynomial.natDegree_zero, Nat.zero_le]
  | case2 n =>
    simpa only [oppositePolePolynomial, Nat.succ_sub_one] using
      Polynomial.natDegree_C_mul_X_pow_le (2 / (n.factorial : ℚ)) n
  | case3 => simp only [oppositePolePolynomial, Polynomial.natDegree_C, Nat.zero_le]
  | case4 p q hne hp
    hq =>
    rw [oppositePolePolynomial.eq_4 a p q hne, Nat.succ_sub_one]
    exact
      (Polynomial.natDegree_C_mul_le _ _).trans
        (Polynomial.natDegree_add_le_of_degree_le (hp.trans (Nat.sub_le _ _)) hq)

/-- The translated high mass polynomial has at most `K.degree + 2` relevant coefficients. -/
public theorem high_mass_shifted_degree (K : HighGaussianKernel) (b : ℚ) :
    ((highGaussianMassPolynomial K).comp (Polynomial.X + Polynomial.C b)).natDegree ≤
      K.degree + 1 := by
  apply Polynomial.natDegree_comp_le.trans
  rw [Polynomial.natDegree_X_add_C, mul_one]
  unfold highGaussianMassPolynomial
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  refine (Polynomial.natDegree_C_mul_le _ _).trans ((opposite_poly_degree _ _ _).trans ?_)
  exact (Nat.sub_le_sub_right (Nat.sub_le (K.degree + 2) j) 1).trans_eq (by rfl)

/-- The K196 tail sign requires only the translated coefficients of degrees zero through 57. -/
public theorem k196_shifted_coeff_nonpos
    (hc :
      ∀ j ∈ Finset.range 58,
        ((highGaussianMassPolynomial .k196).comp (Polynomial.X + Polynomial.C (75 / 2))).coeff j ≤
          0) :
    ∀ j,
      ((highGaussianMassPolynomial .k196).comp (Polynomial.X + Polynomial.C (75 / 2))).coeff j ≤
        0 := by
  intro j
  by_cases hj : j < 58
  · exact hc j (Finset.mem_range.mpr hj)
  have hd :
    ((highGaussianMassPolynomial .k196).comp (Polynomial.X + Polynomial.C (75 / 2))).natDegree ≤
      57 :=
    high_mass_shifted_degree .k196 (75 / 2)
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt
      (hd.trans_lt (lt_of_lt_of_le (by decide : 57 < 58) (Nat.le_of_not_gt hj)))]

end PseudoPrime.PrimeTestBounds.MillerRabin
