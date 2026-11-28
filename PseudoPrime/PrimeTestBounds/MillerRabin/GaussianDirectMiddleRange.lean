/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianDirectCutoff
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleScale
import PseudoPrime.Analysis.ExponentialFixedPointBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # Cutoff logarithm ranges for the direct middle kernels -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The positive Taylor subtotal at a rational endpoint. -/
private def middleExpSum (x : ℚ) (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range n, x ^ k / (k.factorial : ℚ)

/-- Transfer the rational upper comparison through the geometric Taylor tail. -/
private theorem middle_exp_le {x U : ℚ} (hx : 0 ≤ x) (hsize : x / 41 ≤ 1 / 2)
    (h : middleExpSum x 40 + x ^ 40 / (Nat.factorial 40 : ℚ) * 2 ≤ U) :
    Real.exp (x : ℝ) ≤ (U : ℝ) := by
  have hs := Rat.cast_le (K := ℝ).mpr hsize
  have hr := Rat.cast_le (K := ℝ).mpr h
  simp only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] at hs
  simp only [middleExpSum, Rat.cast_add, Rat.cast_sum, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_natCast, Rat.cast_ofNat] at hr
  exact
    (Analysis.exp_le_taylor_add_two_next (n := 40) (Rat.cast_nonneg.mpr hx)
          (by
            norm_num only at hs ⊢
            exact hs)).trans
      hr

/-- Transfer the rational lower comparison using only the positive Taylor subtotal. -/
private theorem middle_le_exp {x V : ℚ} (hx : 0 ≤ x) (h : V ≤ middleExpSum x 40) :
    (V : ℝ) ≤ Real.exp (x : ℝ) := by
  have hr := Rat.cast_le (K := ℝ).mpr h
  simp only [middleExpSum, Rat.cast_sum, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast] at hr
  exact hr.trans (Real.sum_le_exp_of_nonneg (Rat.cast_nonneg.mpr hx) 40)

/-- A positive scaled radius between two exponential anchors yields the
corresponding closed logarithmic interval for the squared cutoff. -/
private theorem middle_log_sq_mem {L a b : ℝ} (hL : 0 < L)
    (ha : Real.exp (a / 2) ≤ gaussianDirectScale * L)
    (hb : gaussianDirectScale * L ≤ Real.exp (b / 2)) :
    Real.log ((gaussianDirectScale * L) ^ 2) ∈ Set.Icc a b := by
  have hp := mul_pos (by norm_num only [gaussianDirectScale] : 0 < gaussianDirectScale) hL
  have hl := (Real.le_log_iff_exp_le hp).mpr ha
  have hu := (Real.log_le_iff_le_exp hp).mpr hb
  rw [Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  exact ⟨by linarith only [hl], by linarith only [hu]⟩

/-- The direct K141 cutoff has logarithm in its certified two-cell range. -/
public theorem gaussian_k141_log_range {L : ℝ} (h : L ∈ Set.Icc (42410 : ℝ) 400000) :
    Real.log ((gaussianDirectScale * L) ^ 2) ∈ Set.Icc (20 : ℝ) 25 := by
  have he :=
    middle_exp_le (x := 10) (U := 22027) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have hm := middle_le_exp (x := 25 / 2) (V := 268337) (by decide +kernel) (by decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at he hm
  apply middle_log_sq_mem ((by norm_num only : (0 : ℝ) < 42410).trans_le h.1)
  · norm_num only
    exact
      he.trans
        ((by norm_num only [gaussianDirectScale] : (22027 : ℝ) ≤ gaussianDirectScale * 42410).trans
          (mul_le_mul_of_nonneg_left h.1 (by norm_num only [gaussianDirectScale])))
  · exact
      (mul_le_mul_of_nonneg_left h.2 (by norm_num only [gaussianDirectScale])).trans
        ((by norm_num only [gaussianDirectScale] :
              gaussianDirectScale * 400000 ≤ (268337 : ℝ)).trans
          hm)

/-- The direct K156 cutoff has logarithm in its certified seven-cell range. -/
public theorem gaussian_k156_log_range {L : ℝ} (h : L ∈ Set.Icc (400000 : ℝ) 7000000) :
    Real.log ((gaussianDirectScale * L) ^ 2) ∈ Set.Icc (24 : ℝ) (121 / 4) := by
  have he :=
    middle_exp_le (x := 12) (U := 162755) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
  have hm := middle_le_exp (x := 121 / 8) (V := 3704281) (by decide +kernel) (by decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at he hm
  apply middle_log_sq_mem ((by norm_num only : (0 : ℝ) < 400000).trans_le h.1)
  · norm_num only
    exact
      he.trans
        ((by norm_num only [gaussianDirectScale] :
              (162755 : ℝ) ≤ gaussianDirectScale * 400000).trans
          (mul_le_mul_of_nonneg_left h.1 (by norm_num only [gaussianDirectScale])))
  · rw [show (121 / 4 : ℝ) / 2 = 121 / 8 by norm_num only]
    exact
      (mul_le_mul_of_nonneg_left h.2 (by norm_num only [gaussianDirectScale])).trans
        ((by norm_num only [gaussianDirectScale] :
              gaussianDirectScale * 7000000 ≤ (3704281 : ℝ)).trans
          hm)

/-- A half-unit residual margin for K141 retains a quarter unit after reducing
its linear coefficient by `7 / 10^8` on the certified logarithm range. -/
public theorem k141_lowered_residual {s R : ℝ} (hs : s ≤ 25) (hR : 1 / 2 < R) :
    1 / 4 < R - (7 / 10 ^ 8) * Real.exp (s / 2) := by
  have h :=
    middle_exp_le (x := 25 / 2) (U := 270000) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
  simp only [Rat.cast_div, Rat.cast_ofNat] at h
  have he :=
    (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hs (by norm_num only : (0 : ℝ) ≤ 2))).trans h
  linarith only [he, hR]

/-- A half-unit residual margin for K156 retains a quarter unit after reducing
its linear coefficient by `6 / 10^8` on the certified logarithm range. -/
public theorem k156_lowered_residual {s R : ℝ} (hs : s ≤ 121 / 4) (hR : 1 / 2 < R) :
    1 / 4 < R - (6 / 10 ^ 8) * Real.exp (s / 2) := by
  have h :=
    middle_exp_le (x := 121 / 8) (U := 3710000) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
  simp only [Rat.cast_div, Rat.cast_ofNat] at h
  have ht : s / 2 ≤ 121 / 8 := by linarith only [hs]
  have he := (Real.exp_le_exp.mpr ht).trans h
  linarith only [he, hR]

private theorem middle_comp_exp_upper : Real.exp (7 / 4) ≤ (575460267600574 : ℝ) / 10 ^ 14 := by
  have h :=
    middle_exp_le (x := 7 / 4) (U := 575460267600574 / 10 ^ 14) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow] using h

private theorem middle_comp_scale_bound {k I U V : ℝ} (hk : 0 ≤ k) (hU : 0 ≤ U) (hI : I ≤ U)
    (hV : k * (575460268 / 10 ^ 8) * U ≤ V) : k * Real.exp (7 / 4) * I ≤ V := by
  calc
    _ ≤ k * Real.exp (7 / 4) * U := mul_le_mul_of_nonneg_left hI (mul_nonneg hk (Real.exp_pos _).le)
    _ ≤ k * (575460268 / 10 ^ 8) * U :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (middle_comp_exp_upper.trans (by norm_num only)) hk) hU
    _ ≤ _ := hV

/-- The certified K141 integral upper bound preserves the reduced slope
when the stated lower bound on the uncompensated slope holds. -/
public theorem k141_comp_slope_le {I Δ : ℝ} (hI : I ≤ 864821009060099 / 10 ^ 18)
    (hΔ : 72170863822 / 10 ^ 11 ≤ Δ) :
    7215924929 / 10 ^ 10 ≤ Δ - 4 * ((middleK141Norm : ℝ) * Real.exp (7 / 4) * I) := by
  have h :=
    middle_comp_scale_bound (k := (middleK141Norm : ℝ)) (V := 29032486 / 10 ^ 12)
      (by norm_num only [middleK141Norm, Rat.cast_div, Rat.cast_ofNat]) (by norm_num only) hI
      (by norm_num only [middleK141Norm, Rat.cast_div, Rat.cast_ofNat])
  linarith only [h, hΔ]

/-- The certified K156 integral upper bound preserves the reduced slope
when the stated lower bound on the uncompensated slope holds. -/
public theorem k156_comp_slope_le {I Δ : ℝ} (hI : I ≤ 693849645969795 / 10 ^ 18)
    (hΔ : 72170932589 / 10 ^ 11 ≤ Δ) :
    721603265 / 10 ^ 9 ≤ Δ - 4 * ((middleK156Norm : ℝ) * Real.exp (7 / 4) * I) := by
  have h :=
    middle_comp_scale_bound (k := (middleK156Norm : ℝ)) (V := 26510090 / 10 ^ 12)
      (by norm_num only [middleK156Norm, Rat.cast_div, Rat.cast_ofNat]) (by norm_num only) hI
      (by norm_num only [middleK156Norm, Rat.cast_div, Rat.cast_ofNat])
  linarith only [h, hΔ]

/-- A rational exponential upper bound at the K141 pole shift. -/
private theorem middle_delta_exp_seven : Real.exp 7 ≤ (109663315842846 : ℝ) / 10 ^ 11 := by
  have h :=
    middle_exp_le (x := 7) (U := 109663315842846 / 10 ^ 11) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
  simpa only [Rat.cast_ofNat, Rat.cast_div, Rat.cast_pow] using h

/-- A rational exponential upper bound at the K156 pole shift. -/
private theorem middle_delta_exp_high : Real.exp (343 / 40) ≤ (529755143822010 : ℝ) / 10 ^ 11 := by
  have h :=
    middle_exp_le (x := 343 / 40) (U := 529755143822010 / 10 ^ 11) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
  simpa only [Rat.cast_ofNat, Rat.cast_div, Rat.cast_pow] using h

/-- Combine endpoint and exponential bounds into a lower bound for the main slope. -/
private theorem middle_delta_of_caps {x k p P K U V D : ℝ} (hk : 0 ≤ k) (hp : 0 ≤ p) (hpP : p ≤ P)
    (hK : K ≤ V) (hV : 0 ≤ V) (hU : Real.exp x ≤ U)
    (hD : D ≤ 4 * k * p / U - (575460267600574 / 10 ^ 14) * V) :
    D ≤ 4 * k * Real.exp (-x) * P - Real.exp (7 / 4) * K := by
  have hx := Real.exp_pos x
  have hk4 : 0 ≤ 4 * k := mul_nonneg (by norm_num only) hk
  have hmain : 4 * k * p / U ≤ 4 * k * Real.exp (-x) * P := by
    calc
      _ ≤ 4 * k * p / Real.exp x := div_le_div_of_nonneg_left (mul_nonneg hk4 hp) hx hU
      _ = 4 * k * Real.exp (-x) * p := by rw [Real.exp_neg, div_eq_mul_inv, mul_right_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_left hpP (mul_nonneg hk4 (Real.exp_pos _).le)
  have hcost : Real.exp (7 / 4) * K ≤ (575460267600574 / 10 ^ 14) * V :=
    (mul_le_mul_of_nonneg_left hK (Real.exp_pos _).le).trans
      (mul_le_mul_of_nonneg_right middle_comp_exp_upper hV)
  exact hD.trans (sub_le_sub hmain hcost)

/-- A lower bound for the K141 slope from bounds on the Laplace endpoint and kernel value. -/
public theorem k141_delta_of_caps {P K : ℝ} (hP : 501705565937097 / 10 ^ 10 ≤ P)
    (hK : K ≤ 60099052035064 / 10 ^ 15) :
    72170863822 / 10 ^ 11 ≤
      4 * (middleK141Norm : ℝ) * Real.exp (-7) * P - Real.exp (7 / 4) * K := by
  exact
    middle_delta_of_caps (by norm_num only [middleK141Norm, Rat.cast_ofNat, Rat.cast_div])
      (by norm_num only) hP hK (by norm_num only) middle_delta_exp_seven
      (by norm_num only [middleK141Norm, Rat.cast_ofNat, Rat.cast_div])

/-- A lower bound for the K156 slope from bounds on the Laplace endpoint and kernel value. -/
public theorem k156_delta_of_caps {P K : ℝ} (hP : 212966675878402 / 10 ^ 9 ≤ P)
    (hK : K ≤ 60114635943415 / 10 ^ 15) :
    72170932589 / 10 ^ 11 ≤
      4 * (middleK156Norm : ℝ) * Real.exp (-(343 / 40)) * P - Real.exp (7 / 4) * K := by
  exact
    middle_delta_of_caps (by norm_num only [middleK156Norm, Rat.cast_ofNat, Rat.cast_div])
      (by norm_num only) hP hK (by norm_num only) middle_delta_exp_high
      (by norm_num only [middleK156Norm, Rat.cast_ofNat, Rat.cast_div])

end PseudoPrime.PrimeTestBounds.MillerRabin
