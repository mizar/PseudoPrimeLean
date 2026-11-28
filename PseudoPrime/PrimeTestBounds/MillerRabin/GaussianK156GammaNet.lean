/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK156GammaTaylor
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK156GammaTaylor
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK156GammaWidth
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK156LowerCharge
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleGammaMajorant
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleIntCurvature

/-! # Common-denominator form of the K156 Gamma polynomial after pole subtraction -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Store the Taylor pole row over a common denominator. Each nonconstant numerator
is obtained by multiplying the checked Taylor output by the complementary factors. -/
private def poleRow : MiddleIntRow :=
  ⟨BData.den * 20 ^ 79 * (80 : ℕ).factorial,
    Array.ofFn fun i : Fin 81 ↦
      if i.val = 0 then 0
      else
        output[i.val - 1]?.getD 0 * 20 ^ (80 - i.val) * ((80 : ℕ).factorial / i.val.factorial : ℕ)⟩

/-- The positive coefficient scale of the Taylor row. -/
private theorem pole_den_pos : 0 < poleRow.den := by decide +kernel

/-- A nonconstant entry of the common-denominator row recovers its Taylor coefficient. -/
private theorem pole_num_eq (i : ℕ) (hi : i < 81) (hi₀ : i ≠ 0) :
    (poleRow.num i : ℚ) / poleRow.den =
      (output[i - 1]?.getD 0 : ℚ) / ((BData.den : ℚ) * 20 ^ (i - 1)) / i.factorial := by
  have hi₁ : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr hi₀
  have hi₂ : i ≤ 80 := Nat.le_of_lt_succ hi
  have hp : (i - 1) + (80 - i) = 79 := by rw [← Nat.sub_add_comm hi₁, Nat.add_sub_of_le hi₂]
  have hf : ((80 : ℕ).factorial / i.factorial) * i.factorial = (80 : ℕ).factorial :=
    Nat.div_mul_cancel (Nat.factorial_dvd_factorial hi₂)
  have hfq := congrArg (fun n : ℕ ↦ (n : ℚ)) hf
  rw [Nat.cast_mul] at hfq
  have hF : (((80 : ℕ).factorial / i.factorial : ℕ) : ℚ) ≠ 0 := by
    apply Nat.cast_ne_zero.mpr
    intro hz
    rw [hz, Nat.zero_mul] at hf
    exact Nat.factorial_ne_zero 80 hf.symm
  have h₂₀ : (20 : ℚ) ≠ 0 := by norm_num only
  simp only [poleRow, MiddleIntRow.num, Array.getElem?_ofFn, dite_eq_left hi, Option.getD_some,
    ite_eq_right hi₀, Int.cast_mul, Int.cast_pow, Int.cast_ofNat, Int.cast_natCast]
  rw [← hfq, ← hp, pow_add]
  let c : ℚ := 20 ^ (80 - i) * ((80 : ℕ).factorial / i.factorial : ℕ)
  rw [div_div]
  calc
    _ = ((output[i - 1]?.getD 0 : ℚ) * c) / (((BData.den : ℚ) * 20 ^ (i - 1) * i.factorial) * c) :=
      by
      dsimp only [c]
      congr 1 <;> ac_rfl
    _ = _ := mul_div_mul_right _ _ (mul_ne_zero (pow_ne_zero _ h₂₀) hF)

/-- The common-denominator pole row represents the checked Taylor polynomial. -/
private theorem pole_row_poly : poleRow.poly 80 = middleK156SecondPole := by
  ext i
  by_cases hi : i < 81
  · rw [poleRow.poly_coeff (Nat.le_of_lt_succ hi), middleK156SecondPole,
      Polynomial.ofFn_coeff_eq_val_of_lt _ hi]
    by_cases hz : i = 0
    · subst i
      simp only [poleRow, MiddleIntRow.num, Array.getElem?_ofFn,
        dite_eq_left (show 0 < 81 from by decide), Option.getD_some, ite_true, Int.cast_zero,
        zero_div]
    · rw [ite_eq_right hz]
      exact pole_num_eq i hi hz
  · simp only [MiddleIntRow.poly, middleK156SecondPole,
      Polynomial.ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt hi)]

/-- The K156 Gamma upper polynomial with its Taylor pole subtracted.
The middle residual uses this single polynomial before taking absolute values. -/
public noncomputable def middleK156GammaNet : Polynomial ℚ :=
  middleGammaUpperPoly middleK156Profile middleK156GammaRow - middleK156SecondPole

/-- The value of the net polynomial is the difference in the contour upper bound. -/
public theorem middle_k156_gamma_net_eval (z : ℝ) :
    (middleK156GammaNet.map (Rat.castHom ℝ)).eval z =
      ((middleGammaUpperPoly middleK156Profile middleK156GammaRow).map (Rat.castHom ℝ)).eval z -
        (middleK156SecondPole.map (Rat.castHom ℝ)).eval z := by
  simp only [middleK156GammaNet, Polynomial.map_sub, Polynomial.eval_sub]

/-- Zero-padding the shorter upper row preserves the polynomial. -/
private theorem upper_row_padded : upperRow.poly 80 = upperRow.poly 51 := by
  have hs : upperRow.nums.size ≤ 52 := by
    simp only [upperRow, MiddleIntRow.gammaUpper, Array.size_ofFn, le_refl]
  ext i
  rw [upperRow.poly_coeff_all 80 (hs.trans (by decide)), upperRow.poly_coeff_all 51 hs]

/-- Subtract the pole on the coefficient level using common denominators. -/
private def netRow : MiddleIntRow :=
  upperRow.add 80 (poleRow.scale (-1) 1)

/-- The output of the integer subtraction is the net Gamma polynomial. -/
private theorem net_row_poly : netRow.poly 80 = middleK156GammaNet := by
  rw [netRow, MiddleIntRow.poly_add _ _ _ (by decide +kernel) (by decide +kernel), upper_row_padded,
    upper_row_poly, MiddleIntRow.poly_scale, pole_row_poly]
  simp only [middleK156GammaNet, Int.cast_neg, Int.cast_one, div_one, Polynomial.C_neg,
    Polynomial.C_1, neg_mul, one_mul, sub_eq_add_neg]

/-- Enclose both the net value and its slope at a rational physical endpoint. -/
private theorem net_endpoint_contains (a b : ℤ) (hb : 0 < b) :
    let Q := middleK156GammaNet.map (Rat.castHom ℝ)
    (netRow.evalInterval 80 a b).Contains netRow.den (Q.eval ((a : ℝ) / b)) ∧
      ((netRow.deriv 79).evalInterval 79 a b).Contains netRow.den
        (Q.derivative.eval ((a : ℝ) / b)) := by
  intro Q
  have hd : 0 < netRow.den := by decide +kernel
  have h := netRow.eval_interval_contains 80 a b hd hb
  have h' := netRow.deriv_interval_contains 79 a b hd hb
  rw [net_row_poly] at h
  rw [show 79 + 1 = 80 from rfl, net_row_poly] at h'
  exact ⟨h, h'⟩

/-- The integer Horner evaluation at the first physical endpoint is below the next integer. -/
private theorem first_endpoint_tick :
    (netRow.evalInterval 80 55 2).upper ≤ 13334415210965077162309636787 * netRow.den := by
  decide +kernel

/-- The first K156 net endpoint has the certified integer upper bound. -/
public theorem middle_k156_gamma_left_le :
    (middleK156GammaNet.map (Rat.castHom ℝ)).eval (55 / 2) ≤ 13334415210965077162309636787 := by
  have h := (net_endpoint_contains 55 2 (by decide)).1.2
  have hden : (0 : ℝ) < netRow.den := Int.cast_pos.mpr (by decide +kernel)
  have hu :
    ((netRow.evalInterval 80 55 2).upper : ℝ) / netRow.den ≤ 13334415210965077162309636787 := by
    apply (div_le_iff₀ hden).mpr
    simpa only [Int.cast_mul, Int.cast_ofNat] using (Int.cast_le (R := ℝ)).mpr first_endpoint_tick
  simpa only [Int.cast_ofNat] using h.trans hu

/-- With the physical exponential and normalization included, the first K156 net
endpoint contributes at most 486 millionths. -/
public theorem middle_k156_gamma_left_scaled :
    (middleK156Norm : ℝ) * Real.exp (-(49 / 20 : ℝ) * (55 / 2)) *
        (middleK156GammaNet.map (Rat.castHom ℝ)).eval (55 / 2) ≤
      486 / 10 ^ 6 := by
  have h :=
    middle_gamma_width_scaled (κ := middleK156Norm) (cap := 13334415210965077162309636787) (R :=
      486 / 10 ^ 6) (y := (49 / 20 : ℝ) * (55 / 2)) 2695 (by decide +kernel) (by norm_num only)
      (by norm_num only) (by simpa only [Rat.cast_ofNat] using middle_k156_gamma_left_le)
      (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow, neg_mul] using h

/-- Translate the net row to the left endpoint of the K156 physical range. -/
private def netLocalRow : MiddleIntRow :=
  netRow.shift 80 55 2

/-- Bound net curvature after subtracting the second pole at the coefficient level. -/
private theorem net_curvature_le (p d : ℤ) (hp : 0 ≤ p) (hd : 0 < d) {t : ℝ} (ht : 0 ≤ t)
    (ht' : t ≤ (p : ℝ) / d) :
    let Q := middleK156GammaNet.comp (Polynomial.X + Polynomial.C (55 / 2 : ℚ))
    |(gaussianLocalCurv (Q.map (Rat.castHom ℝ)) (49 / 20) 1).eval t| ≤
      (netLocalRow.curvCap 80 49 20 p d : ℝ) / netLocalRow.den := by
  intro Q
  have h := netLocalRow.curv_cap_le 80 49 20 p d (by decide +kernel) (by decide) hp hd ht ht'
  have hq : netLocalRow.poly 80 = Q := by
    dsimp only [netLocalRow, Q]
    rw [netRow.poly_shift 80 55 2 (by decide +kernel) (by decide), net_row_poly]
    norm_num only [Int.cast_ofNat]
  rw [hq] at h
  simpa only [Int.cast_ofNat] using h

end PseudoPrime.PrimeTestBounds.MillerRabin
