/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleGammaWidth
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleGammaMajorant
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleIntCurvature
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK141LowerCharge
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK141LowerCharge

/-! # Certified K141 Gamma width budgets -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rounded radius weights with denominator ten to the sixteenth. -/
private def weights0 : Array Int :=
  #[1130786164283, 1413482705354, 2662350979936, 5566682720529, 11164545575759, 20994492872632,
    37308237212606, 63367753235293, 103859120218469, 165467579251689, 257675279945260,
    393867749162580, 592906912891481, 881673281045120, 1306845927744725, 2037028955944887,
    5570637188692901, 44937121076386902, 876092576006775002, 14038253362667965978,
    330804429530160109696, 5892751761557472442267, 152826488664515692737054,
    2981724430299971117150558, 84360209542728380705816317, 1789034639602077992625413482,
    54834136174642097085092133079, 1255902316958271803628519496216,
    41454606947965836121169905783763, 1019792681370021668663110404434869,
    36065508044730135856314497726279728, 948407193674119941557184334822187282]

/-- Check that all rounded weights enclose the computable radius majorants. -/
private theorem weights0_checked :
    (∀ j : Fin 32,
      middleGammaRadiusWeight (5 / 4) middleK141GammaWidth j.val ≤
        ((weights0[j.val]?.getD 0 : ℤ) : ℚ) / 10 ^ 16) := by
  decide +kernel

/-- The rounded weights are nonnegative throughout the checked range. -/
private theorem weights0_nonneg : ∀ j : Fin 32, 0 ≤ weights0[j.val]?.getD 0 := by decide +kernel

/-- Transfer the rounded radius checks to the analytic coefficient widths. -/
private theorem weights0_sound (j : ℕ) (hj : j ≤ 31) :
    middleGammaWidthWeight (5 / 4) middleK141GammaRow j ≤
      ((weights0[j]?.getD 0 : ℤ) : ℚ) / 10 ^ 16 := by
  exact
    (middle_gamma_radius_weight_le (by norm_num only) middleK141GammaRow _
          middle_k141_gamma_width_le j).trans
      (weights0_checked ⟨j, Nat.lt_succ_of_le hj⟩)

/-- The centered integer dot product fits the rational allowance of this cell. -/
private theorem cell0_dot :
    middleGammaWidthDot (BData.shift 31 99 4) 31 (fun i ↦ weights0[i]?.getD 0) ≤
      42036022198506142 * ((BData.shift 31 99 4).den * 10 ^ 16) := by
  decide +kernel

/-- The rational Gamma coefficient-width budget for the cell centered at `99/4`. -/
public theorem middle_k141_gamma_width_cell0 :
    middleGammaWidthBudget middleK141Profile (99 / 4) (5 / 4) middleK141GammaRow ≤
      42036022198506142 := by
  have h :=
    middle_gamma_width_int_cap BData 31 99 4 (by decide) (by decide) (5 / 4) middleK141GammaRow
      (fun i ↦ weights0[i]?.getD 0) (D := 10 ^ 16) (u := 42036022198506142) (v := 1) (by decide)
      (by decide) weights0_sound (fun j hj ↦ weights0_nonneg ⟨j, Nat.lt_succ_of_le hj⟩)
      (by simpa only [mul_one] using cell0_dot)
  simpa only [middleK141Profile, Int.cast_ofNat, Int.cast_one, div_one] using h

/-- The centered integer dot product fits the rational allowance of this cell. -/
private theorem cell1_dot :
    middleGammaWidthDot (BData.shift 31 109 4) 31 (fun i ↦ weights0[i]?.getD 0) ≤
      6238698850586334185 * ((BData.shift 31 109 4).den * 10 ^ 16) := by
  decide +kernel

/-- The rational Gamma coefficient-width budget for the cell centered at `109/4`. -/
public theorem middle_k141_gamma_width_cell1 :
    middleGammaWidthBudget middleK141Profile (109 / 4) (5 / 4) middleK141GammaRow ≤
      6238698850586334185 := by
  have h :=
    middle_gamma_width_int_cap BData 31 109 4 (by decide) (by decide) (5 / 4) middleK141GammaRow
      (fun i ↦ weights0[i]?.getD 0) (D := 10 ^ 16) (u := 6238698850586334185) (v := 1) (by decide)
      (by decide) weights0_sound (fun j hj ↦ weights0_nonneg ⟨j, Nat.lt_succ_of_le hj⟩)
      (by simpa only [mul_one] using cell1_dot)
  simpa only [middleK141Profile, Int.cast_ofNat, Int.cast_one, div_one] using h

/-- The Gamma width correction costs at most one millionth on this cell
after multiplication by the normalized physical exponential. -/
public theorem middle_k141_gamma_scaled0 {z : ℝ} (hz : 47 / 2 ≤ z) :
    (middleK141Norm : ℝ) * Real.exp (-(2 : ℝ) * z) *
        (middleGammaWidthBudget middleK141Profile (99 / 4) (5 / 4) middleK141GammaRow : ℝ) ≤
      1 / 10 ^ 6 := by
  have hy : (1880 : ℝ) / 40 ≤ (2 : ℝ) * z := by linarith only [hz]
  have h :=
    middle_gamma_width_scaled (κ := middleK141Norm) (cap := 42036022198506142) (R := 1 / 10 ^ 6)
      1880 (by decide +kernel) (by norm_num only) hy
      ((Rat.cast_le (K := ℝ)).mpr middle_k141_gamma_width_cell0) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, Rat.cast_pow, neg_mul] using h

/-- The Gamma width correction costs at most one millionth on this cell
after multiplication by the normalized physical exponential. -/
public theorem middle_k141_gamma_scaled1 {z : ℝ} (hz : 26 ≤ z) :
    (middleK141Norm : ℝ) * Real.exp (-(2 : ℝ) * z) *
        (middleGammaWidthBudget middleK141Profile (109 / 4) (5 / 4) middleK141GammaRow : ℝ) ≤
      1 / 10 ^ 6 := by
  have hy : (2080 : ℝ) / 40 ≤ (2 : ℝ) * z := by linarith only [hz]
  have h :=
    middle_gamma_width_scaled (κ := middleK141Norm) (cap := 6238698850586334185) (R := 1 / 10 ^ 6)
      2080 (by decide +kernel) (by norm_num only) hy
      ((Rat.cast_le (K := ℝ)).mpr middle_k141_gamma_width_cell1) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, Rat.cast_pow, neg_mul] using h

/-- A common denominator for the order-zero endpoint, higher-order grid,
and exact pole contributions. -/
private def upperDen : ℕ :=
  (middleK141GammaRow 0).2.den * 10 ^ 16 * 3 ^ 32

/-- The input endpoint denominators divide the chosen scale at every retained order. -/
private theorem upper_den_dvd : ∀ j : Fin 32, (middleK141GammaRow j.val).2.den ∣ upperDen := by
  decide +kernel

/-- The derivative sum's upper polynomial as a shared integer row. -/
private def upperRow : MiddleIntRow :=
  BData.gammaUpper (middleGammaWeightRow 31 upperDen middleK141GammaRow) 31

/-- The shared row represents the upper polynomial used by the contour bound. -/
private theorem upper_row_poly :
    upperRow.poly 31 = middleGammaUpperPoly middleK141Profile middleK141GammaRow := by
  exact
    BData.gamma_upper_poly _ 31 _ (by decide) fun j hj ↦
      middle_gamma_weight_row_eq 31 upperDen _ (by decide +kernel) j hj (upper_den_dvd ⟨j, hj⟩)

/-- Both endpoint enclosures use the shared integer row for the Gamma upper polynomial. -/
private theorem upper_endpoint_contains (a b : ℤ) (hb : 0 < b) :
    let Q := (middleGammaUpperPoly middleK141Profile middleK141GammaRow).map (Rat.castHom ℝ)
    (upperRow.evalInterval 31 a b).Contains upperRow.den (Q.eval ((a : ℝ) / b)) ∧
      ((upperRow.deriv 30).evalInterval 30 a b).Contains upperRow.den
        (Q.derivative.eval ((a : ℝ) / b)) := by
  intro Q
  have hd : 0 < upperRow.den := by decide +kernel
  have h := upperRow.eval_interval_contains 31 a b hd hb
  have h' := upperRow.deriv_interval_contains 30 a b hd hb
  rw [upper_row_poly] at h
  rw [show 30 + 1 = 31 from rfl, upper_row_poly] at h'
  exact ⟨h, h'⟩

/-- Translate the shared derivative-sum row once to the left endpoint of the physical range. -/
private def upperLocalRow : MiddleIntRow :=
  upperRow.shift 31 47 2

/-- The translated upper row supplies the curvature cap at any cell right endpoint. -/
private theorem upper_curvature_le (p d : ℤ) (hp : 0 ≤ p) (hd : 0 < d) {t : ℝ} (ht : 0 ≤ t)
    (ht' : t ≤ (p : ℝ) / d) :
    let Q :=
      (middleGammaUpperPoly middleK141Profile middleK141GammaRow).comp
        (Polynomial.X + Polynomial.C (47 / 2 : ℚ))
    |(gaussianLocalCurv (Q.map (Rat.castHom ℝ)) (2 / 1) 1).eval t| ≤
      (upperLocalRow.curvCap 31 2 1 p d : ℝ) / upperLocalRow.den := by
  intro Q
  have h := upperLocalRow.curv_cap_le 31 2 1 p d (by decide +kernel) (by decide) hp hd ht ht'
  have hq : upperLocalRow.poly 31 = Q := by
    dsimp only [upperLocalRow, Q]
    rw [upperRow.poly_shift 31 47 2 (by decide +kernel) (by decide), upper_row_poly]
    norm_num only [Int.cast_ofNat]
  rw [hq] at h
  simpa only [Int.cast_ofNat, Int.cast_one] using h

end PseudoPrime.PrimeTestBounds.MillerRabin
