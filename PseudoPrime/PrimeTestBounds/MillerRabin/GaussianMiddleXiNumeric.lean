/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleXiBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleMassCoeffs
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleXiBounds
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleWeights
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleMassCoeffs
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100Bounds

/-! # Fixed-point checker for the middle principal zero mass -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The rational majorant at one lower endpoint, reading the shared numerator row. -/
private def headRat (a : ℚ) (d : ℕ) (row : Array ℚ) (t : ℚ) : ℚ :=
  ∑ j ∈ Finset.range (d + 1), max 0 (row[j]?.getD 0) / (a ^ 2 + t ^ 2) ^ (d + 2 - j)

/-- The rational multiplier on the inverse-square tail. -/
private def tailRat (d : ℕ) (row : Array ℚ) : ℚ :=
  ∑ j ∈ Finset.range (d + 1), max 0 (row[j]?.getD 0) / 100 ^ (2 * (d + 1 - j))

/-- Round one rational bound upwards to a millionth. -/
private def upTicks (q : ℚ) : ℤ :=
  ⌈10 ^ 6 * q⌉

/-- Each rounding step bounds the corresponding real value. -/
private theorem le_up_ticks (q : ℚ) : (q : ℝ) ≤ (upTicks q : ℝ) / 10 ^ 6 := by
  apply (le_div_iff₀ (by norm_num only : (0 : ℝ) < 10 ^ 6)).mpr
  have h := Rat.cast_le (K := ℝ).mpr (Int.le_ceil (10 ^ 6 * q))
  simpa only [upTicks, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_intCast, mul_comm] using
    h

/-- Compute the upper bound in millionths. The 29 ordinate denominators are
kept separate until after rounding, and the numerator convolution is shared. -/
public def middleXiTicks (a κ : ℚ) (d : ℕ) (f : ℕ → ℚ) : ℤ :=
  let row := middleNormTable a d f
  (∑ i : Fin 29,
      upTicks (2 * κ * headRat a d row (AnalyticNumberTheory.RiemannZeta.lowZero100Lower i))) +
    upTicks (κ * tailRat d row * (13 / 1000))

/-- The checker supplies an upper bound for the normalized Xi mass from
a compact polynomial coefficient row. -/
public theorem middle_xi_le_ticks (Q : Polynomial ℚ) (a κ : ℚ) {d : ℕ} (f : ℕ → ℚ)
    (ha : 2 ≤ (a : ℝ)) (hκ : 0 ≤ κ) (hd : 1 ≤ d) (hQ : Q.natDegree ≤ d)
    (hf : ∀ j ≤ d, f j = Q.coeff j) (hRH : RiemannHypothesis) :
    (κ : ℝ) * (middleXiMass Q a d).re ≤ (middleXiTicks a κ d f : ℝ) / 10 ^ 6 := by
  let row := middleNormTable a d f
  have hrow (j : ℕ) (hj : j ∈ Finset.range (d + 1)) :
    row[j]?.getD 0 = (normSqPolynomial a Q).coeff j :=
    middle_norm_coeff Q a d f hQ hf j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
  have hh (i : Fin 29) :
    (headRat a d row (AnalyticNumberTheory.RiemannZeta.lowZero100Lower i) : ℝ) =
      middleMassHeightCap Q a d (middleZeroLower i) := by
    simp only [headRat, middleMassHeightCap, middleZeroLower, Rat.cast_sum, Rat.cast_div,
      Rat.cast_max, Rat.cast_zero, Rat.cast_pow, Rat.cast_add]
    exact Finset.sum_congr rfl fun j hj ↦ by rw [hrow j hj]
  have ht : (tailRat d row : ℝ) = middleMassHeightTail Q a d 100 := by
    simp only [tailRat, middleMassHeightTail, Rat.cast_sum, Rat.cast_div, Rat.cast_max,
      Rat.cast_zero, Rat.cast_pow, Rat.cast_ofNat]
    exact Finset.sum_congr rfl fun j hj ↦ by rw [hrow j hj]
  refine
    (mul_le_mul_of_nonneg_left (middle_xi_mass_le Q a ha hd hQ hRH) (Rat.cast_nonneg.mpr hκ)).trans
      ?_
  simp only [middleXiTicks, ← show row = middleNormTable a d f from rfl, Int.cast_add, Int.cast_sum,
    add_div, Finset.sum_div]
  rw [mul_add, ← mul_assoc, Finset.mul_sum, ← mul_assoc]
  apply add_le_add
  · apply Finset.sum_le_sum
    intro i _
    have h :=
      le_up_ticks (2 * κ * headRat a d row (AnalyticNumberTheory.RiemannZeta.lowZero100Lower i))
    simpa only [Rat.cast_mul, Rat.cast_ofNat, hh, mul_comm (2 : ℝ)] using h
  · have h := le_up_ticks (κ * tailRat d row * (13 / 1000))
    simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat, ht] using h

end PseudoPrime.PrimeTestBounds.MillerRabin
