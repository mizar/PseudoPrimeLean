/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.BernsteinCompensation
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighCompensationPartition
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianLaplaceSignCell
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleReflection
import all PseudoPrime.Analysis.BernsteinCompensation
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighCompensationPartition
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianLaplaceSignCell
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Order.Interval.Set.Infinite
import PseudoPrime.Analysis.BernsteinBounds

/-! # Exact compensation on cells with nonpositive Bernstein coefficients -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- If every Bernstein coefficient is nonpositive, clipping simply negates
the polynomial. In particular, the compensation and its derivative can
be integrated using the original profile on a merged negative cell. -/
public theorem bernstein_compensation_eq_neg (P : Polynomial ℚ) (n : ℕ) (hP : P.natDegree ≤ n)
    (hs : ∀ i ≤ n, Analysis.bernsteinRatCoeff P n i ≤ 0) :
    Analysis.bernsteinCompensation P n = -(P.map (Rat.castHom ℝ)) := by
  apply Polynomial.eq_of_infinite_eval_eq
  refine (Set.Icc_infinite (zero_lt_one : (0 : ℝ) < 1)).mono (fun x hx ↦ ?_)
  rw [Set.mem_ofPred_eq, Polynomial.eval_neg, Polynomial.eval_map,
    Analysis.compensation_eval P n ⟨x, hx⟩, Analysis.bernstein_rat_coeff_eval P n hP ⟨x, hx⟩, ←
    Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [max_eq_right (neg_nonneg.mpr (Rat.cast_nonpos.mpr (hs i (Nat.le_of_lt_succ i.isLt)))),
    neg_mul]

/-- The physical compensation on a nonpositive cell is the negated
original profile, with the affine coordinate eliminated. -/
public theorem high_cell_compensation_eq_neg (K : HighGaussianKernel) {a b : ℚ} (hab : a < b)
    (hc :
      ∀ i ≤ 2 * K.degree + 3,
        Analysis.bernsteinRatCoeff
            (K.ratProfile.comp (Polynomial.C (b - a) * Polynomial.X + Polynomial.C a))
            (2 * K.degree + 3) i ≤
          0)
    (t : ℝ) : highCellCompensation K a (b - a) t = -K.realProfile.eval t := by
  have hw : (0 : ℝ) < ((b - a : ℚ) : ℝ) := Rat.cast_pos.mpr (sub_pos.mpr hab)
  rw [highCellCompensation,
    bernstein_compensation_eq_neg _ _
      (Analysis.bernstein_affine_degree _ _ (high_rat_profile_degree K) a b) hc,
    Polynomial.eval_neg, Polynomial.map_comp, Polynomial.eval_comp, high_comp_profile_map]
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
    Rat.coe_castHom, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    mul_comm ((b - a : ℚ) : ℝ), div_mul_cancel₀ _ hw.ne', sub_add_cancel]

/-- Every signed endpoint factor evaluates the same Laplace polynomial.
The coefficient row of this polynomial can be checked once for all cells. -/
private theorem signed_tail_factor_moment (P : Polynomial ℚ) (s a : ℚ) :
    signedTailFactor P s a = (middleMomentPoly P s 0).eval a := by
  have hQ := (Polynomial.taylor_apply a P).symm
  simp only [signedTailFactor, hQ, Polynomial.natDegree_taylor, Polynomial.taylor_coeff,
    middleMomentPoly, Polynomial.C_0, add_zero, Polynomial.comp_X, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_C]

/-- Bound the main integral on a nonpositive cell by just two signed
Laplace factors and outward enclosures for the endpoint exponentials. -/
public theorem high_cell_comp_signed_le (K : HighGaussianKernel) {s a b : ℚ} (hs : 0 < s)
    (ha : 0 ≤ a) (hab : a < b)
    (hc :
      ∀ i ≤ 2 * K.degree + 3,
        Analysis.bernsteinRatCoeff
            (K.ratProfile.comp (Polynomial.C (b - a) * Polynomial.X + Polynomial.C a))
            (2 * K.degree + 3) i ≤
          0)
    (la ua lb ub : ℚ)
    (hleft : (la : ℝ) ≤ Real.exp (-(s : ℝ) * (a : ℝ)) ∧ Real.exp (-(s : ℝ) * (a : ℝ)) ≤ (ua : ℝ))
    (hright : (lb : ℝ) ≤ Real.exp (-(s : ℝ) * (b : ℝ)) ∧ Real.exp (-(s : ℝ) * (b : ℝ)) ≤ (ub : ℝ)) :
    let f := (middleMomentPoly K.ratProfile s 0).eval a
    let g := (middleMomentPoly K.ratProfile s 0).eval b
    (∫ t in (a : ℝ)..(b : ℝ), Real.exp (-(s : ℝ) * t) * highCellCompensation K a (b - a) t) ≤
      ((max (lb * g) (ub * g) - min (la * f) (ua * f) : ℚ) : ℝ) := by
  have hp :=
    bernstein_cell_nonpos K.ratProfile (high_rat_profile_degree K) hab
      (fun i ↦ hc i (Nat.le_of_lt_succ i.isLt))
  have he := negative_cell_le_endpoint_ranges _ hs ha hab.le hp _ _ _ _ hleft hright
  simp only [signed_tail_factor_moment] at he
  refine (intervalIntegral.integral_congr (fun t ht ↦ ?_)).trans_le he
  have hab' : (a : ℝ) ≤ (b : ℝ) := Rat.cast_le.mpr hab.le
  have h := hp t (Set.uIcc_of_le hab' ▸ ht)
  rw [high_cell_compensation_eq_neg K hab hc, max_eq_right (neg_nonneg.mpr h),
    high_comp_profile_map]

/-- For a very short cell, the left endpoint exponential times the
unweighted compensation integral bounds the main charge. Only the sum of
the clipped coefficients is needed for the unweighted integral. -/
public theorem high_cell_comp_mean_le (K : HighGaussianKernel) {s a h E : ℚ} (hs : 0 ≤ s)
    (hh : 0 < h) (hE : Real.exp (-(s : ℝ) * (a : ℝ)) ≤ (E : ℝ)) :
    let n := 2 * K.degree + 3
    let P := K.ratProfile.comp (Polynomial.C h * Polynomial.X + Polynomial.C a)
    (∫ t in (a : ℝ)..(a : ℝ) + (h : ℝ), Real.exp (-(s : ℝ) * t) * highCellCompensation K a h t) ≤
      (E : ℝ) * (h : ℝ) * (∑ i : Fin (n + 1), (max 0 (-Analysis.bernsteinRatCoeff P n i.val) : ℚ)) /
        (n + 1) := by
  intro n P
  have hP : P.natDegree ≤ n := by
    have h := Analysis.bernstein_affine_degree K.ratProfile n (high_rat_profile_degree K) a (a + h)
    rwa [add_sub_cancel_left] at h
  have hh' : 0 < (h : ℝ) := Rat.cast_pos.mpr hh
  have hshift := Analysis.bernstein_compensation_shift_le P n hP hh' hE
  have hm := Analysis.bernstein_compensation_exp_le P n 0 hP hh' (Rat.cast_nonneg.mpr hs)
  simp only [Nat.mul_zero, Nat.zero_add, Finset.sum_range_one, pow_zero, Nat.factorial_zero,
    Nat.cast_one, div_one, one_mul, pow_one, Nat.add_zero] at hm
  have hweight (i : Fin (n + 1)) : (n.choose i.val : ℝ) / (n.choose i.val : ℝ) = 1 :=
    div_self (Nat.cast_ne_zero.mpr (Nat.choose_pos (Nat.le_of_lt_succ i.isLt)).ne')
  simp only [hweight, one_div, ← div_eq_mul_inv, ← Finset.sum_mul] at hm
  have hE' : 0 ≤ (E : ℝ) := (Real.exp_pos _).le.trans hE
  refine hshift.trans ((mul_le_mul_of_nonneg_left hm hE').trans_eq ?_)
  rw [Rat.cast_sum]
  ring

/-- A common upper bound for the absolute variation coefficients gives a
rectangular integral bound, with the exponential taken at the left endpoint. -/
private theorem high_cell_comp_var_max (K : HighGaussianKernel) {a h E M : ℚ} (hh : 0 < h)
    (hp : 0 ≤ K.pole) (hM : 0 ≤ M) (hE : Real.exp (-(K.pole : ℝ) * (a : ℝ)) ≤ E)
    (hc :
      let n := 2 * K.degree + 3
      let P := K.ratProfile.comp (Polynomial.C h * Polynomial.X + Polynomial.C a)
      ∀ i : Fin (n + 1),
        |Analysis.bernsteinVariationDirect n i.val (K.pole - 1 / 2) h
              (fun j ↦ max 0 (-Analysis.bernsteinRatCoeff P n j))| ≤
          M) :
    (∫ t in (a : ℝ)..(a : ℝ) + (h : ℝ), variationIntegrand K a h t) ≤ (h : ℝ) * E * M := by
  let n := 2 * K.degree + 3
  let P := K.ratProfile.comp (Polynomial.C h * Polynomial.X + Polynomial.C a)
  let C := Analysis.bernsteinCompensation P n
  have hh' : 0 < (h : ℝ) := Rat.cast_pos.mpr hh
  have ha : (a : ℝ) ≤ (a : ℝ) + (h : ℝ) := le_add_of_nonneg_right hh'.le
  have hle (t : ℝ) (ht : t ∈ Set.Icc (a : ℝ) ((a : ℝ) + h)) :
    variationIntegrand K a h t ≤ (E : ℝ) * M := by
    let u : Set.Icc (0 : ℝ) 1 :=
      ⟨(t - a) / h, div_nonneg (sub_nonneg.mpr ht.1) hh'.le,
        (div_le_one hh').mpr (sub_le_iff_le_add'.mpr ht.2)⟩
    have hv := Analysis.bernstein_variation_abs_le P n (K.pole - 1 / 2) h u
    simp only [Analysis.bernstein_variation_direct_eq] at hv
    let c := fun i : Fin (n + 1) ↦
      |(Analysis.bernsteinVariationDirect n i.val (K.pole - 1 / 2) h
            (fun j ↦ max 0 (-Analysis.bernsteinRatCoeff P n j)) :
          ℝ)|
    have hm :=
      Analysis.bernstein_sum_le n c u (M : ℝ)
        (fun i ↦ by
          dsimp only [c]
          rw [← Rat.cast_abs]
          exact Rat.cast_le.mpr (hc i))
    have he :=
      (Real.exp_le_exp.mpr
            (mul_le_mul_of_nonpos_left ht.1 (neg_nonpos.mpr (Rat.cast_nonneg.mpr hp)))).trans
        hE
    exact
      (mul_le_mul_of_nonneg_left (hv.trans hm) (Real.exp_pos _).le).trans
        (mul_le_mul_of_nonneg_right he (Rat.cast_nonneg.mpr hM))
  have hcont : Continuous (variationIntegrand K a h) := by
    have hu : Continuous (fun t : ℝ ↦ (t - (a : ℝ)) / (h : ℝ)) :=
      (continuous_id.sub continuous_const).div_const _
    exact
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
        (((C.continuous.comp hu).const_mul _).sub
            ((C.derivative.continuous.comp hu).const_mul _)).abs
  have hbound :=
    intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) ha (hcont.intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _) hle
  simpa only [intervalIntegral.integral_const, add_sub_cancel_left, smul_eq_mul, mul_assoc] using
    hbound

end PseudoPrime.PrimeTestBounds.MillerRabin
