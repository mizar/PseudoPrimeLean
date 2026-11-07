/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.GaussianMomentGridNumerators

/-! # Uniform validity of Gaussian fixed-point grid inputs -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- On the nonpositive half of the grid, the certified inner exponential
is at least the fixed-point scale. Its signed numerator is nonnegative. -/
theorem gaussian_grid_inner_ge_scale (i : ℕ) (hi : i ≤ 127) :
    10 ^ 24 ≤ gaussianMomentGridInner i := by
  have hiZ : (i : ℤ) ≤ 127 := by exact_mod_cast hi
  have ha : 0 ≤ 127 - (i : ℤ) := sub_nonneg.mpr hiZ
  rw [gaussianMomentGridInner, Analysis.expFixedPointSignedLower, ite_eq_left ha]
  exact Analysis.scale_le_expFixedPointLowerSum _ _ _ _ (by norm_num only)

/-- Every outer grid numerator for tilt 1 or 3 is nonnegative.
On the negative half, the inner lower endpoint offsets the negative tilt;
on the nonnegative half all summands are nonnegative. -/
theorem gaussian_grid_outer_num_nonneg (i k : ℕ) (hk : k ∈ ({1, 3} : Finset ℕ)) :
    0 ≤ gaussianGridOuterNegNum i k := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl
  · by_cases hi : i < 128
    · have hE : (10 ^ 24 : ℤ) ≤ (gaussianMomentGridInner i : ℤ) := by
        exact_mod_cast gaussian_grid_inner_ge_scale i (Nat.le_of_lt_succ hi)
      rw [gaussianGridOuterNegNum, gaussianGridNearest, ite_eq_left hi]
      norm_num only [Nat.cast_one]
      nlinarith only [hE, sq_nonneg ((i : ℤ) - 119)]
    · have hiZ : (128 : ℤ) ≤ i := by exact_mod_cast (Nat.le_of_not_gt hi)
      have hE : (0 : ℤ) ≤ (gaussianMomentGridInner i : ℤ) := Nat.cast_nonneg _
      rw [gaussianGridOuterNegNum, gaussianGridNearest, ite_eq_right hi]
      norm_num only [Nat.cast_one]
      nlinarith only [hiZ, hE, sq_nonneg ((i : ℤ) - 128)]
  · by_cases hi : i < 128
    · have hE : (10 ^ 24 : ℤ) ≤ (gaussianMomentGridInner i : ℤ) := by
        exact_mod_cast gaussian_grid_inner_ge_scale i (Nat.le_of_lt_succ hi)
      rw [gaussianGridOuterNegNum, gaussianGridNearest, ite_eq_left hi]
      norm_num only [Nat.cast_ofNat]
      nlinarith only [hE, sq_nonneg ((i : ℤ) - 103)]
    · have hiZ : (128 : ℤ) ≤ i := by exact_mod_cast (Nat.le_of_not_gt hi)
      have hE : (0 : ℤ) ≤ (gaussianMomentGridInner i : ℤ) := Nat.cast_nonneg _
      rw [gaussianGridOuterNegNum, gaussianGridNearest, ite_eq_right hi]
      norm_num only [Nat.cast_ofNat]
      nlinarith only [hiZ, hE, sq_nonneg ((i : ℤ) - 128)]

/-- Every fixed-point outer endpoint is positive when at least one Taylor term
is retained. The nonnegative outer numerator ensures the sum contains the scale. -/
theorem gaussian_grid_outer_fixed_pos (i k n : ℕ) (hk : k ∈ ({1, 3} : Finset ℕ)) (hn : 0 < n) :
    0 <
      Analysis.expFixedPointSignedLower (gaussianGridOuterNegNum i k) (5120 * 10 ^ 24) (10 ^ 24)
        n := by
  have ha := gaussian_grid_outer_num_nonneg i k hk
  rw [Analysis.expFixedPointSignedLower, ite_eq_left ha]
  exact
    (by norm_num only : 0 < 10 ^ 24).trans_le (Analysis.scale_le_expFixedPointLowerSum _ _ _ _ hn)

/-- Each inner endpoint on the 256-cell grid is at most 81 times its scale.
The exponent is at most four and `exp(4) < 3^4`. -/
theorem gaussian_grid_inner_le_81_scale (i : ℕ) (hi : i < 256) :
    gaussianMomentGridInner i ≤ 81 * 10 ^ 24 := by
  have hexp4 : Real.exp (4 : ℝ) ≤ 81 := by
    rw [show (4 : ℝ) = (4 : ℕ) * 1 by norm_num only, Real.exp_nat_mul]
    exact
      (pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 4).trans_eq (by norm_num only)
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have ha : -((-4 : ℝ) + ((i : ℝ) + 1) / 32) ≤ 4 := by linarith only [hi0]
  have h := (gaussian_grid_inner_lower i hi).trans ((Real.exp_le_exp.mpr ha).trans hexp4)
  have hR : (gaussianMomentGridInner i : ℝ) ≤ (81 : ℝ) * 10 ^ 24 := by
    dsimp only [gaussianMomentGridInner]
    apply (div_le_iff₀ (by norm_num only : (0 : ℝ) < 10 ^ 24)).1
    norm_num only at h ⊢
    exact h
  exact_mod_cast hR

/-- Every outer numerator on the grid, for tilt 1 or 3, is at most 200 times
the common denominator. Bound the cell square, tilt, and inner endpoint. -/
theorem gaussian_grid_outer_num_le (i k : ℕ) (hi : i < 256) (hk : k ∈ ({1, 3} : Finset ℕ)) :
    gaussianGridOuterNegNum i k ≤ (200 : ℤ) * (5120 * 10 ^ 24) := by
  have hiN : i ≤ 255 := Nat.le_of_lt_succ hi
  have hiZ : (i : ℤ) ≤ 255 := by exact_mod_cast hiN
  have hi0 : (0 : ℤ) ≤ i := Nat.cast_nonneg i
  have hE : (gaussianMomentGridInner i : ℤ) ≤ 81 * 10 ^ 24 := by
    exact_mod_cast gaussian_grid_inner_le_81_scale i hi
  have hnear : -(128 : ℤ) ≤ gaussianGridNearest i ∧ gaussianGridNearest i ≤ 128 := by
    unfold gaussianGridNearest
    split_ifs <;> constructor <;> linarith only [hiZ, hi0]
  have hs : gaussianGridNearest i ^ 2 ≤ (128 : ℤ) ^ 2 := by
    have hm :=
      mul_nonneg (sub_nonneg.mpr hnear.2)
        (show 0 ≤ 128 + gaussianGridNearest i by linarith only [hnear.1])
    nlinarith only [hm]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl
  · dsimp only [gaussianGridOuterNegNum]
    norm_num only [Nat.cast_one]
    nlinarith only [hE, hiZ, hs]
  · dsimp only [gaussianGridOuterNegNum]
    norm_num only [Nat.cast_ofNat]
    nlinarith only [hE, hiZ, hs]

/-- The outer exponents satisfy the signed Taylor size condition with 401 terms.
The uniform numerator bound is strictly within the admissible range. -/
theorem gaussian_grid_outer_size_401 (i k : ℕ) (hi : i < 256) (hk : k ∈ ({1, 3} : Finset ℕ)) :
    (|((gaussianGridOuterNegNum i k : ℤ) : ℝ)| / (5120 * 10 ^ 24 : ℕ)) / (401 + 1 : ℕ) ≤ 1 / 2 := by
  have h0 : (0 : ℝ) ≤ gaussianGridOuterNegNum i k := by
    exact_mod_cast gaussian_grid_outer_num_nonneg i k hk
  have hu : (gaussianGridOuterNegNum i k : ℝ) ≤ (200 : ℝ) * (5120 * 10 ^ 24) := by
    exact_mod_cast gaussian_grid_outer_num_le i k hi hk
  rw [abs_of_nonneg h0]
  norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
  norm_num only at hu ⊢
  linarith only [hu]

/-- The two Gaussian moment integrals on [-4,4] are bounded by explicit
256-term rational sums, with no certificate hypotheses. Uniform size and
positivity estimates validate all signed fixed-point exponential endpoints. -/
theorem gaussian_grid_256_executable_bounds :
    (∫ v in (-4 : ℝ)..4, Analysis.gaussianGammaProfileIntegrand (21 / 10) v) ≤
        ∑ i ∈ Finset.range 256,
          (1 / 32 : ℝ) *
            ((113 / 200 : ℝ) *
              ((10 ^ 24 : ℝ) /
                (Analysis.expFixedPointSignedLower (gaussianGridOuterNegNum i 1) (5120 * 10 ^ 24)
                    (10 ^ 24) 401 :
                  ℝ))) ∧
      (∫ v in (-4 : ℝ)..4, gaussianEndpointDensity (21 / 10) v) ≤
        ∑ i ∈ Finset.range 256,
          (1 / 32 : ℝ) *
            ((113 / 200 : ℝ) *
              ((10 ^ 24 : ℝ) /
                (Analysis.expFixedPointSignedLower (gaussianGridOuterNegNum i 3) (5120 * 10 ^ 24)
                    (10 ^ 24) 401 :
                  ℝ))) := by
  apply gaussian_grid_256_numerator_bounds (n := 401)
  · intro i hi k hk
    exact gaussian_grid_outer_size_401 i k hi hk
  · intro i hi k hk
    exact gaussian_grid_outer_fixed_pos i k 401 hk (by norm_num only)

end PseudoPrime.LLS.PaperStatements
