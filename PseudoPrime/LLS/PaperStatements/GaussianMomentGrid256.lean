/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.GaussianMomentGrid
public import PseudoPrime.Analysis.ExponentialFixedPointConversions

/-! # The 256-cell Gaussian moment grid -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- The `i`th endpoint of the uniform 256-cell grid from -4 to 4.
The spacing is 1/32. -/
noncomputable def gaussianMomentGridPoint (i : ℕ) : ℝ :=
  -4 + (i : ℝ) / 32

/-- Executable fixed-point lower endpoint for the inner exponential of cell `i`.
The scale is 10^24 and the signed Taylor certificate uses 121 terms. -/
def gaussianMomentGridInner (i : ℕ) : ℕ :=
  Analysis.expFixedPointSignedLower (127 - (i : ℤ)) 32 (10 ^ 24) 121

/-- For every cell of the 256-cell grid on [-4,4], the executable fixed-point
value is a lower bound for the inner exponential at its right endpoint.
The input range satisfies the signed Taylor certificate size condition. -/
theorem gaussian_grid_inner_lower (i : ℕ) (hi : i < 256) :
    (Analysis.expFixedPointSignedLower (127 - (i : ℤ)) 32 (10 ^ 24) 121 : ℝ) / (10 ^ 24 : ℝ) ≤
      Real.exp (-((-4 : ℝ) + ((i : ℝ) + 1) / 32)) := by
  have hiN : i ≤ 255 := Nat.le_of_lt_succ hi
  have hiR : (i : ℝ) ≤ 255 := by exact_mod_cast hiN
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have ha : |(127 : ℝ) - i| ≤ 128 := by
    rw [abs_le]
    constructor <;> linarith only [hiR, hi0]
  have hsize : (|((127 - (i : ℤ) : ℤ) : ℝ)| / 32) / (121 + 1 : ℕ) ≤ 1 / 2 := by
    norm_num only [Int.cast_sub, Int.cast_ofNat, Int.cast_natCast, Nat.cast_add, Nat.cast_one,
      Nat.cast_ofNat]
    linarith only [ha]
  have h :=
    Analysis.exp_fixed_signed_lower_div (127 - (i : ℤ)) 32 (10 ^ 24) 121 (by norm_num only)
      (by norm_num only) hsize
  norm_num only [Int.cast_sub, Int.cast_ofNat, Int.cast_natCast, Nat.cast_ofNat, Nat.cast_pow] at h
  have he : ((127 : ℝ) - i) / 32 = -((-4 : ℝ) + ((i : ℝ) + 1) / 32) := by ring
  rw [he] at h
  norm_num only
  exact h

/-- At cutoff 21/10, upper bounds for the two outer exponentials on the 256
cells bound both Gaussian moments over [-4,4]. The fixed-point inner endpoints
are proved lower bounds, and the square minima are handled uniformly. -/
theorem gaussian_grid_256_bounds {uF uC : ℕ → ℝ}
    (hF :
      ∀ i < 256,
        Real.exp
            (-gaussianCellSquareLower (gaussianMomentGridPoint i)
                  (gaussianMomentGridPoint (i + 1)) -
              (1 / 2 : ℝ) * gaussianMomentGridPoint i -
              (21 / 10 : ℝ) * ((gaussianMomentGridInner i : ℝ) / (10 ^ 24 : ℝ))) ≤
          uF i)
    (hC :
      ∀ i < 256,
        Real.exp
            (-gaussianCellSquareLower (gaussianMomentGridPoint i)
                  (gaussianMomentGridPoint (i + 1)) -
              (3 / 2 : ℝ) * gaussianMomentGridPoint i -
              (21 / 10 : ℝ) * ((gaussianMomentGridInner i : ℝ) / (10 ^ 24 : ℝ))) ≤
          uC i) :
    (∫ v in (-4 : ℝ)..4, Analysis.gaussianGammaProfileIntegrand (21 / 10) v) ≤
        ∑ i ∈ Finset.range 256, (1 / 32 : ℝ) * ((113 / 200 : ℝ) * uF i) ∧
      (∫ v in (-4 : ℝ)..4, gaussianEndpointDensity (21 / 10) v) ≤
        ∑ i ∈ Finset.range 256, (1 / 32 : ℝ) * ((113 / 200 : ℝ) * uC i) := by
  have hp : ∀ i < 256, gaussianMomentGridPoint i ≤ gaussianMomentGridPoint (i + 1) := by
    intro i hi
    dsimp only [gaussianMomentGridPoint]
    norm_num only [Nat.cast_add, Nat.cast_one]
    linarith only
  have he :
    ∀ i < 256,
      (gaussianMomentGridInner i : ℝ) / (10 ^ 24 : ℝ) ≤
        Real.exp (-gaussianMomentGridPoint (i + 1)) := by
    intro i hi
    have h := gaussian_grid_inner_lower i hi
    dsimp only [gaussianMomentGridInner, gaussianMomentGridPoint]
    norm_num only [Nat.cast_add, Nat.cast_one] at h ⊢
    exact h
  have h :=
    gaussian_moment_grid_bounds (p := gaussianMomentGridPoint) (e := fun i ↦
      (gaussianMomentGridInner i : ℝ) / (10 ^ 24 : ℝ)) hp he hF hC
  have h0 : gaussianMomentGridPoint 0 = -4 := by norm_num only [gaussianMomentGridPoint]
  have h256 : gaussianMomentGridPoint 256 = 4 := by norm_num only [gaussianMomentGridPoint]
  rw [h0, h256] at h
  have hd (i : ℕ) : gaussianMomentGridPoint (i + 1) - gaussianMomentGridPoint i = (1 / 32 : ℝ) := by
    dsimp only [gaussianMomentGridPoint]
    norm_num only [Nat.cast_add, Nat.cast_one]
    ring
  simpa only [hd] using h

end PseudoPrime.LLS.PaperStatements
