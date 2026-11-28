/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighNegativeMoment
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186CoarseCert
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186ReflectionCert
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186CoarseMoment

/-! # A coarse H30 bound for the far Gaussian comparison -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The checked row represents the physical polynomial translated to the
cell's left endpoint. -/
private theorem coarse_shift_poly (i : ℕ) :
    ((coarseShift i).poly 83).map (Rat.castHom ℝ) =
      HighGaussianKernel.k186.realProfile.comp
        (Polynomial.X + Polynomial.C (k186MomentLeft i)) := by
  have h := baseRow.poly_shift 83 (35 + 6 * (i : ℤ)) 1 (by decide +kernel) (by decide)
  rw [base_row_poly] at h
  rw [coarseShift, h, Polynomial.map_comp, high_comp_profile_map]
  simp only [Int.cast_one, div_one, Polynomial.map_add, Polynomial.map_X, Polynomial.map_C,
    Rat.coe_castHom, Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast, Rat.cast_add,
    Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast, k186MomentLeft]

/-- The denominator is positive and independent of the integer shift. -/
private theorem coarse_shift_den_pos (i : ℕ) : 0 < (coarseShift i).den := by
  change 0 < baseRow.den * (1 : ℤ) ^ 83
  rw [one_pow, mul_one]
  decide +kernel

/-- The exponential multiplier lies below the reciprocal integer power
used in the checker. -/
private theorem coarse_exp_le (i : ℕ) :
    Real.exp (-(9 / 4 : ℝ) * k186MomentLeft i) ≤ (10 / 27 : ℝ) ^ coarseExponent i := by
  have hn : ((coarseExponent i : ℕ) : ℝ) ≤ (9 / 4 : ℝ) * k186MomentLeft i := by
    have h := Nat.div_mul_le_self (9 * (35 + 6 * i)) 4
    have hr := (Nat.cast_le (α := ℝ)).mpr h
    push_cast only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] at hr
    dsimp only [coarseExponent, k186MomentLeft] at *
    linarith only [hr]
  have he : Real.exp (-1) ≤ (10 / 27 : ℝ) := by
    rw [Real.exp_neg, ← one_div]
    exact
      (one_div_le_one_div_of_le (by norm_num only)
            ((by norm_num only : (27 / 10 : ℝ) ≤ 2.7182818283).trans
              Real.exp_one_gt_d9.le)).trans_eq
        (by norm_num only)
  have h := Real.exp_le_exp.mpr (neg_le_neg hn)
  calc
    _ = Real.exp (-((9 / 4 : ℝ) * k186MomentLeft i)) := by rw [neg_mul]
    _ ≤ Real.exp (-((coarseExponent i : ℕ) : ℝ)) := h
    _ = Real.exp (-1) ^ coarseExponent i := by rw [← mul_neg_one, Real.exp_natCast_mul]
    _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos _).le he _

/-- The shifted derivative coefficient is the signed integer input to
the checker divided by the common denominator. -/
private theorem coarse_derivative_coeff (i j k : ℕ) :
    ((((Polynomial.derivative^[j]) HighGaussianKernel.k186.realProfile).comp
            (Polynomial.X + Polynomial.C (k186MomentLeft i))).coeff
        k) =
      (((coarseShift i).num (k + j) * ((k + j).descFactorial j : ℤ) : ℤ) : ℝ) /
        ((coarseShift i).den : ℝ) := by
  rw [shifted_derivative_coeff, ← coarse_shift_poly, Polynomial.coeff_map]
  have hs : (coarseShift i).nums.size ≤ 83 + 1 := by
    simp only [coarseShift, MiddleIntRow.shift, MiddleIntRow.affine, gaussianAffineRatioRow,
      gaussianAffineIntRow, Array.size_ofFn, le_refl]
  rw [(coarseShift i).poly_coeff_all 83 hs]
  simp only [Rat.coe_castHom, Rat.cast_div, Rat.cast_intCast, Int.cast_mul, Int.cast_natCast]
  ring

/-- The integer cross comparison gives the real cap on one negative moment. -/
private theorem coarse_cell_le (i : Fin 5) (j : Fin 3) :
    let P := (Polynomial.derivative^[j.val]) HighGaussianKernel.k186.realProfile
    (∫ t in k186MomentLeft i..k186MomentLeft i + 6,
        Real.exp (-(9 / 4 : ℝ) * t) * max 0 (-P.eval t)) ≤
      (coarseCaps j i : ℝ) := by
  have h :=
    k186_negative_moment_cell j.val (l := k186MomentLeft i) (w := 6) (by norm_num only)
      (coarse_exp_le i)
  dsimp only at h ⊢
  simp only [coarse_derivative_coeff] at h
  let d := ((coarseShift i).den : ℝ)
  have hd : 0 < d := Int.cast_pos.mpr (coarse_shift_den_pos i)
  have hmax (a : ℝ) : max 0 (-(a / d)) = max 0 (-a) / d := by
    rw [← neg_div, ← max_div_div_right hd.le, zero_div]
  dsimp only [d] at hmax
  simp only [hmax, div_mul_eq_mul_div, ← Finset.sum_div] at h
  have hv :
    (coarseCoeffSum (coarseShift i) j : ℝ) =
      ∑ k ∈ Finset.range 84,
        max 0 (-(((coarseShift i).num (k + j) * ((k + j).descFactorial j : ℤ) : ℤ) : ℝ)) *
          (6 : ℝ) ^ k := by
    simp only [coarseCoeffSum, Int.cast_sum, Int.cast_mul, Int.cast_max, Int.cast_zero,
      Int.cast_neg, Int.cast_pow, Int.cast_ofNat]
  rw [← hv] at h
  refine h.trans ?_
  have hi := Int.cast_le (R := ℝ) |>.mpr (coarse_check i j)
  simp only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat] at hi
  let e := coarseExponent i
  have hp : 0 < (27 : ℝ) ^ e := pow_pos (by norm_num only) _
  calc
    _ = (6 * (coarseCoeffSum (coarseShift i) j : ℝ) * 10 ^ e) / (d * 27 ^ e) := by
      rw [div_pow, div_mul_div_comm, ← mul_div_assoc]
      simp only [d, e, mul_comm (27 ^ coarseExponent i : ℝ)]
      ring
    _ ≤ _ := (div_le_iff₀ (mul_pos hd hp)).mpr (by simpa only [d, e, mul_assoc] using hi)

/-- Sum the five integral caps at each of the first three derivative orders. -/
private theorem coarse_moment_le (j : Fin 3) :
    highNegativeMoment .k186 j ≤ ∑ i ∈ Finset.range 5, (coarseCaps j i : ℝ) := by
  refine k186_negative_moment_le_cells j (fun i ↦ (coarseCaps j i : ℝ)) ?_
  intro i hi
  exact coarse_cell_le ⟨i, Finset.mem_range.mp hi⟩ j

/-- The damped far comparison requires only the coarse bound on H30.
The three moment bounds come from the same five integer shifts. -/
public theorem k186_coarse_moment_caps :
    highNegativeMoment .k186 0 ≤ 2000000000 ∧
      highNegativeMoment .k186 1 ≤ 5000000000 ∧ highNegativeMoment .k186 2 ≤ 10000000000 := by
  have h₀ : highNegativeMoment .k186 0 ≤ 2000000000 := by
    refine (coarse_moment_le 0).trans ?_
    rw [← Int.cast_sum, ← Int.cast_ofNat (R := ℝ) (n := 2000000000)]
    exact Int.cast_le.mpr (by decide +kernel)
  have h₁ : highNegativeMoment .k186 1 ≤ 5000000000 := by
    refine (coarse_moment_le 1).trans ?_
    rw [← Int.cast_sum, ← Int.cast_ofNat (R := ℝ) (n := 5000000000)]
    exact Int.cast_le.mpr (by decide +kernel)
  have h₂ : highNegativeMoment .k186 2 ≤ 10000000000 := by
    refine (coarse_moment_le 2).trans ?_
    rw [← Int.cast_sum, ← Int.cast_ofNat (R := ℝ) (n := 10000000000)]
    exact Int.cast_le.mpr (by decide +kernel)
  exact ⟨h₀, h₁, h₂⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
