/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.GaussianMomentGridFixed

/-! # Integer numerators for Gaussian moment grid certificates -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Numerator over 32 of the grid endpoint nearest zero in cell `i`.
At the zero boundary either endpoint formula has the required square. -/
def gaussianGridNearest (i : ℕ) : ℤ :=
  if i < 128 then (i : ℤ) - 127 else (i : ℤ) - 128

/-- The cell square minimum equals the square of the nearest endpoint numerator.
Separate cells on the two sides of zero and simplify the explicit grid. -/
theorem gaussian_grid_square_eq (i : ℕ) :
    gaussianCellSquareLower (gaussianMomentGridPoint i) (gaussianMomentGridPoint (i + 1)) =
      (((gaussianGridNearest i : ℤ) : ℝ) / 32) ^ 2 := by
  by_cases hi : i < 128
  · have hiN : i ≤ 127 := Nat.le_of_lt_succ hi
    have hiR : (i : ℝ) ≤ 127 := by exact_mod_cast hiN
    have hb : gaussianMomentGridPoint (i + 1) ≤ 0 := by
      dsimp only [gaussianMomentGridPoint]
      norm_num only [Nat.cast_add, Nat.cast_one]
      linarith only [hiR]
    rw [gaussianCellSquareLower, ite_eq_left hb, gaussianGridNearest, ite_eq_left hi]
    dsimp only [gaussianMomentGridPoint]
    norm_num only [Nat.cast_add, Nat.cast_one, Int.cast_sub, Int.cast_natCast, Int.cast_ofNat]
    ring
  · have hiN : 128 ≤ i := Nat.le_of_not_gt hi
    have hiR : (128 : ℝ) ≤ i := by exact_mod_cast hiN
    have ha : 0 ≤ gaussianMomentGridPoint i := by
      dsimp only [gaussianMomentGridPoint]
      linarith only [hiR]
    have hb : ¬gaussianMomentGridPoint (i + 1) ≤ 0 := by
      dsimp only [gaussianMomentGridPoint]
      norm_num only [Nat.cast_add, Nat.cast_one]
      linarith only [hiR]
    rw [gaussianCellSquareLower, ite_eq_right hb, ite_eq_left ha, gaussianGridNearest,
      ite_eq_right hi]
    dsimp only [gaussianMomentGridPoint]
    norm_num only [Int.cast_sub, Int.cast_natCast, Int.cast_ofNat]
    ring

/-- Integer numerator of the negated outer exponential argument for cell `i`.
The tilt numerator `k` is 1 or 3 and the denominator is `5120 * 10^24`.
It combines the nearest endpoint square, tilt, and fixed-point inner endpoint. -/
def gaussianGridOuterNegNum (i k : ℕ) : ℤ :=
  5 * (10 ^ 24 : ℤ) * gaussianGridNearest i ^ 2 + 80 * (10 ^ 24 : ℤ) * (k : ℤ) * ((i : ℤ) - 128) +
    10752 * (gaussianMomentGridInner i : ℤ)

/-- The outer Gaussian cell exponent equals the negation of its integer
numerator divided by the common positive denominator. This identity removes
per-cell real-arithmetic assumptions from the executable certificate. -/
theorem gaussian_grid_outer_num_eq (i k : ℕ) :
    -gaussianCellSquareLower (gaussianMomentGridPoint i) (gaussianMomentGridPoint (i + 1)) -
        ((k : ℝ) / 2) * gaussianMomentGridPoint i -
        (21 / 10 : ℝ) * ((gaussianMomentGridInner i : ℝ) / (10 ^ 24 : ℝ)) =
      -((gaussianGridOuterNegNum i k : ℝ) / (5120 * 10 ^ 24 : ℝ)) := by
  rw [gaussian_grid_square_eq]
  dsimp only [gaussianGridOuterNegNum, gaussianMomentGridPoint]
  push_cast
  ring

/-- Executable integer numerators bound both finite Gaussian moments on [-4,4].
Only the signed Taylor size and positive fixed-point endpoint checks remain.
The grid geometry and rational exponent identities are proved uniformly. -/
theorem gaussian_grid_256_numerator_bounds {n : ℕ}
    (hsize :
      ∀ i < 256,
        ∀ k ∈ ({1, 3} : Finset ℕ),
          (|((gaussianGridOuterNegNum i k : ℤ) : ℝ)| / (5120 * 10 ^ 24 : ℕ)) / (n + 1 : ℕ) ≤ 1 / 2)
    (hpos :
      ∀ i < 256,
        ∀ k ∈ ({1, 3} : Finset ℕ),
          0 <
            Analysis.expFixedPointSignedLower (gaussianGridOuterNegNum i k) (5120 * 10 ^ 24)
              (10 ^ 24) n) :
    (∫ v in (-4 : ℝ)..4, Analysis.gaussianGammaProfileIntegrand (21 / 10) v) ≤
        ∑ i ∈ Finset.range 256,
          (1 / 32 : ℝ) *
            ((113 / 200 : ℝ) *
              ((10 ^ 24 : ℝ) /
                (Analysis.expFixedPointSignedLower (gaussianGridOuterNegNum i 1) (5120 * 10 ^ 24)
                    (10 ^ 24) n :
                  ℝ))) ∧
      (∫ v in (-4 : ℝ)..4, gaussianEndpointDensity (21 / 10) v) ≤
        ∑ i ∈ Finset.range 256,
          (1 / 32 : ℝ) *
            ((113 / 200 : ℝ) *
              ((10 ^ 24 : ℝ) /
                (Analysis.expFixedPointSignedLower (gaussianGridOuterNegNum i 3) (5120 * 10 ^ 24)
                    (10 ^ 24) n :
                  ℝ))) := by
  have h1 : (1 : ℕ) ∈ ({1, 3} : Finset ℕ) := by simp only [Finset.mem_insert, true_or]
  have h3 : (3 : ℕ) ∈ ({1, 3} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, or_true]
  have h :=
    gaussian_grid_256_fixed_bounds (aF := fun i ↦ -gaussianGridOuterNegNum i 1) (aC := fun i ↦
      -gaussianGridOuterNegNum i 3) (bF := fun _ ↦ 5120 * 10 ^ 24) (bC := fun _ ↦ 5120 * 10 ^ 24)
      (n := n) (fun i hi ↦ by norm_num only) (fun i hi ↦ by norm_num only)
      (fun i hi ↦ by simpa only [neg_neg] using hsize i hi 1 h1)
      (fun i hi ↦ by simpa only [neg_neg] using hsize i hi 3 h3)
      (fun i hi ↦ by simpa only [neg_neg] using hpos i hi 1 h1)
      (fun i hi ↦ by simpa only [neg_neg] using hpos i hi 3 h3)
      (fun i hi ↦ by
        simpa only [Nat.cast_one, Int.cast_neg, neg_div, Nat.cast_mul, Nat.cast_pow,
          Nat.cast_ofNat] using gaussian_grid_outer_num_eq i 1)
      (fun i hi ↦ by
        simpa only [Nat.cast_ofNat, Int.cast_neg, neg_div, Nat.cast_mul, Nat.cast_pow] using
          gaussian_grid_outer_num_eq i 3)
  simpa only [neg_neg] using h

end PseudoPrime.LLS.PaperStatements
