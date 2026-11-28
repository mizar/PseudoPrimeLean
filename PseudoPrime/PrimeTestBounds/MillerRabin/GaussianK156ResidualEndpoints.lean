/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleCurvatureCheck
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK156LowerCharge
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleTailBudget
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleResidualProfile

/-! # K156 direct residual endpoint bounds -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The two K156 rational profiles share the coefficient translation at 24. -/
private def costRows : MiddleIntRow × MiddleIntRow :=
  middleInputRows BData 51 24 59 39 20 middleK156Scale

/-- Both K156 integer rows have positive common denominators. -/
private theorem cost_rows_pos : 0 < costRows.1.den ∧ 0 < costRows.2.den := by
  exact
    middle_input_rows_pos BData 51 24 59 39 20 middleK156Scale (by decide) (by decide) (by decide)

/-- The K156 endpoint residue computed at local offset `u / 4`. -/
private def endpointValue (u : ℤ) (j k l : ℕ) : ℚ :=
  middleEndpointLower (721603265 / 10 ^ 9 - 3 / 8 / (519674416 / 10 ^ 9)) (61 / 1000)
    ((u : ℚ) / 4 + 24) (middleRowUpper costRows.1 51 u 4) (middleRowUpper costRows.2 51 u 4) j k l

/-- The rational K156 endpoint computation transfers to its analytic residual. -/
private theorem endpoint_le (u : ℤ) (j k l : ℕ) (hj : (j : ℝ) / 80 = ((u : ℝ) / 4 + 24) / 2)
    (hk : (k : ℝ) / 80 = (49 / 20) * ((u : ℝ) / 4 + 24))
    (hl : (l : ℝ) / 80 = (49 / 20 - 1 / 2) * ((u : ℝ) / 4 + 24)) (hkp : 0 < middleTailExpDen k)
    (hlp : 0 < middleTailExpDen l) :
    (endpointValue u j k l : ℝ) ≤
      gaussianMidResidual (721603265 / 10 ^ 9 - 3 / 8 / gaussianDirectScale) 0 (61 / 1000)
        (middleResidualRates (49 / 20))
        (middleRatProfiles (49 / 20) (7 / 2) (middleK156Scale : ℝ)
          (middleK156Profile.map (Rat.castHom ℝ))
          ((middleMomentPoly middleK156Profile (59 / 20) 0).map (Rat.castHom ℝ)))
        ((u : ℝ) / 4 + 24) := by
  have hi :=
    middle_input_rows_eval BData 51 24 59 39 20 middleK156Scale (by decide) (by decide) (by decide)
      (by decide) ((u : ℝ) / 4)
  norm_num only [Rat.cast_add, Rat.cast_div, Rat.cast_ofNat] at hi
  have hu := middle_row_upper_le costRows.1 51 u 4 cost_rows_pos.1 (by decide) hi.1
  have hv := middle_row_upper_le costRows.2 51 u 4 cost_rows_pos.2 (by decide) hi.2
  have hU : 0 ≤ middleRowUpper costRows.1 51 u 4 :=
    div_nonneg (Int.cast_nonneg_iff.mpr (le_max_left _ _))
      (Int.cast_nonneg_iff.mpr cost_rows_pos.1.le)
  have hV : 0 ≤ middleRowUpper costRows.2 51 u 4 :=
    div_nonneg (Int.cast_nonneg_iff.mpr (le_max_left _ _))
      (Int.cast_nonneg_iff.mpr cost_rows_pos.2.le)
  have hx : (((u : ℚ) / 4 + 24 : ℚ) : ℝ) = (u : ℝ) / 4 + 24 := by
    simp only [Rat.cast_add, Rat.cast_div, Rat.cast_intCast, Rat.cast_ofNat]
  have h :=
    middle_endpoint_lower_le (721603265 / 10 ^ 9 - 3 / 8 / (519674416 / 10 ^ 9)) (61 / 1000)
      ((u : ℚ) / 4 + 24) _ _ (49 / 20) _ j k l (by decide +kernel) hU hV (hx ▸ hj) (hx ▸ hk)
      (hx ▸ hl) hkp hlp (hx ▸ hu) (hx ▸ hv)
  simpa only [endpointValue, hx, Rat.cast_sub, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat,
    gaussianDirectScale, middleK156Profile] using h

/-- The outward rational comparison for local offset 0/4. -/
private theorem endpoint_check_0 : (-40 : ℚ) ≤ endpointValue 0 960 4704 3744 := by decide +kernel

/-- The outward rational comparison for local offset 4/4. -/
private theorem endpoint_check_4 : (-40 : ℚ) ≤ endpointValue 4 1000 4900 3900 := by decide +kernel

/-- The outward rational comparison for local offset 8/4. -/
private theorem endpoint_check_8 : (-40 : ℚ) ≤ endpointValue 8 1040 5096 4056 := by decide +kernel

/-- The outward rational comparison for local offset 12/4. -/
private theorem endpoint_check_12 : (-40 : ℚ) ≤ endpointValue 12 1080 5292 4212 := by decide +kernel

/-- The outward rational comparison for local offset 16/4. -/
private theorem endpoint_check_16 : (-40 : ℚ) ≤ endpointValue 16 1120 5488 4368 := by decide +kernel

/-- The outward rational comparison for local offset 20/4. -/
private theorem endpoint_check_20 : (-40 : ℚ) ≤ endpointValue 20 1160 5684 4524 := by decide +kernel

/-- The outward rational comparison for local offset 24/4. -/
private theorem endpoint_check_24 : (-44 : ℚ) ≤ endpointValue 24 1200 5880 4680 := by decide +kernel

/-- The outward rational comparison for local offset 25/4. -/
private theorem endpoint_check_25 : (-44 : ℚ) ≤ endpointValue 25 1210 5929 4719 := by decide +kernel

/-- The K156 rational residual has verified lower bounds at its eight endpoints. -/
public theorem middle_k156_residual_endpoints :
    let F :=
      gaussianMidResidual (721603265 / 10 ^ 9 - 3 / 8 / gaussianDirectScale) 0 (61 / 1000)
        (middleResidualRates (49 / 20))
        (middleRatProfiles (49 / 20) (7 / 2) (middleK156Scale : ℝ)
          (middleK156Profile.map (Rat.castHom ℝ))
          ((middleMomentPoly middleK156Profile (59 / 20) 0).map (Rat.castHom ℝ)))
    (-40 : ℝ) ≤ F 24 ∧
      (-40 : ℝ) ≤ F 25 ∧
      (-40 : ℝ) ≤ F 26 ∧
      (-40 : ℝ) ≤ F 27 ∧
      (-40 : ℝ) ≤ F 28 ∧ (-40 : ℝ) ≤ F 29 ∧ (-44 : ℝ) ≤ F 30 ∧ (-44 : ℝ) ≤ F (121 / 4) := by
  intro F
  have h0 :=
    ((Rat.cast_le (K := ℝ)).mpr endpoint_check_0).trans
      (endpoint_le 0 960 4704 3744 (by norm_num only) (by norm_num only) (by norm_num only)
        (by decide +kernel) (by decide +kernel))
  have h4 :=
    ((Rat.cast_le (K := ℝ)).mpr endpoint_check_4).trans
      (endpoint_le 4 1000 4900 3900 (by norm_num only) (by norm_num only) (by norm_num only)
        (by decide +kernel) (by decide +kernel))
  have h8 :=
    ((Rat.cast_le (K := ℝ)).mpr endpoint_check_8).trans
      (endpoint_le 8 1040 5096 4056 (by norm_num only) (by norm_num only) (by norm_num only)
        (by decide +kernel) (by decide +kernel))
  have h12 :=
    ((Rat.cast_le (K := ℝ)).mpr endpoint_check_12).trans
      (endpoint_le 12 1080 5292 4212 (by norm_num only) (by norm_num only) (by norm_num only)
        (by decide +kernel) (by decide +kernel))
  have h16 :=
    ((Rat.cast_le (K := ℝ)).mpr endpoint_check_16).trans
      (endpoint_le 16 1120 5488 4368 (by norm_num only) (by norm_num only) (by norm_num only)
        (by decide +kernel) (by decide +kernel))
  have h20 :=
    ((Rat.cast_le (K := ℝ)).mpr endpoint_check_20).trans
      (endpoint_le 20 1160 5684 4524 (by norm_num only) (by norm_num only) (by norm_num only)
        (by decide +kernel) (by decide +kernel))
  have h24 :=
    ((Rat.cast_le (K := ℝ)).mpr endpoint_check_24).trans
      (endpoint_le 24 1200 5880 4680 (by norm_num only) (by norm_num only) (by norm_num only)
        (by decide +kernel) (by decide +kernel))
  have h25 :=
    ((Rat.cast_le (K := ℝ)).mpr endpoint_check_25).trans
      (endpoint_le 25 1210 5929 4719 (by norm_num only) (by norm_num only) (by norm_num only)
        (by decide +kernel) (by decide +kernel))
  norm_num only [Rat.cast_neg, Rat.cast_ofNat, Int.cast_ofNat,
    Int.cast_zero] at h0 h4 h8 h12 h16 h20 h24 h25
  dsimp only [F]
  norm_num only
  exact ⟨h0, h4, h8, h12, h16, h20, h24, h25⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
