/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK156ResidualEndpoints
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK156ResidualEndpoints
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK156LowerCharge
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleResidualProfile
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleTailBudget

/-! # The full K156 direct middle interval -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The K156 rational decay profiles used in its derivative checks. -/
private noncomputable def k156Profiles : Fin 2 → Polynomial ℝ :=
  middleRatProfiles (49 / 20) (7 / 2) (middleK156Scale : ℝ) (middleK156Profile.map (Rat.castHom ℝ))
    ((middleMomentPoly middleK156Profile (59 / 20) 0).map (Rat.castHom ℝ))

/-- Total curvature cap at the right local offset, using the left grid indices. -/
private def curvatureValue (u : ℤ) (j k : ℕ) : ℚ :=
  middleCurvUpper costRows.1 51 49 20 u 4 / middleTailExpDen j +
    middleCurvUpper costRows.2 51 39 20 u 4 / middleTailExpDen k

/-- Transfer the K156 integer comparisons to the signed residual curvature. -/
private theorem curvature_le {x l : ℝ} (u : ℤ) (j k : ℕ) (hu : 0 ≤ u) (hx : 24 ≤ x) (hl : l ≤ x)
    (hxu : x - 24 ≤ (u : ℝ) / 4) (hj : (j : ℝ) / 80 = (49 / 20) * l)
    (hk : (k : ℝ) / 80 = (39 / 20) * l) (hjp : 0 < middleTailExpDen j)
    (hkp : 0 < middleTailExpDen k) :
    gaussianMidResidualCurv (721603265 / 10 ^ 9 - 3 / 8 / gaussianDirectScale) (61 / 1000)
        (middleResidualRates (49 / 20)) k156Profiles x ≤
      (curvatureValue u j k : ℝ) := by
  have hrow (t : ℝ) :=
    middle_input_rows_eval BData 51 24 59 39 20 middleK156Scale (by decide) (by decide) (by decide)
      (by decide) t
  norm_num only [Rat.cast_add, Rat.cast_div, Rat.cast_ofNat] at hrow
  have hrow₀ (t : ℝ) :
    ((costRows.1.poly 51).map (Rat.castHom ℝ)).eval t = (k156Profiles 0).eval (t + 24) := by
    simpa only [k156Profiles, middleK156Profile, costRows] using (hrow t).1
  have hrow₁ (t : ℝ) :
    ((costRows.2.poly 51).map (Rat.castHom ℝ)).eval t = (k156Profiles 1).eval (t + 24) := by
    simpa only [k156Profiles, middleK156Profile, costRows] using (hrow t).2
  have hl' : l ≤ x - 24 + 24 := by rwa [sub_add_cancel]
  have ht := sub_nonneg.mpr hx
  have h₀ :=
    middle_row_decay_curv_le costRows.1 51 49 20 u 4 j cost_rows_pos.1 (by decide) (by decide) hu
      (by decide) ht hxu hl' (by simpa only [Int.cast_ofNat] using hj) hjp hrow₀
  have h₁ :=
    middle_row_decay_curv_le costRows.2 51 39 20 u 4 k cost_rows_pos.2 (by decide) (by decide) hu
      (by decide) ht hxu hl' (by simpa only [Int.cast_ofNat] using hk) hkp hrow₁
  have h :=
    gaussian_mid_curv_le_decay
      (show 721603265 / 10 ^ 9 - 3 / 8 / gaussianDirectScale ≤ 0 by
        norm_num only [gaussianDirectScale])
      (by norm_num only : (0 : ℝ) ≤ 61 / 1000) (middleResidualRates (49 / 20)) k156Profiles x
  have er : middleResidualRates (49 / 20) 1 = (39 / 20 : ℝ) := by
    change 49 / 20 - 1 / 2 = (39 / 20 : ℝ)
    norm_num only
  rw [gaussianDecaySum, Fin.sum_univ_two, er] at h
  simp only [middleResidualRates, Fin.cases_zero] at h
  simp only [sub_add_cancel, Int.cast_ofNat] at h₀ h₁
  rw [curvatureValue, Rat.cast_add]
  linarith only [h, h₀, h₁]

/-- The integer curvature comparison for the cell ending at local offset 8/4. -/
private theorem curvature_check_8 : curvatureValue 8 4704 3744 ≤ 8 := by decide +kernel

/-- The integer curvature comparison for the cell ending at local offset 12/4. -/
private theorem curvature_check_12 : curvatureValue 12 5096 4056 ≤ 2 := by decide +kernel

/-- The integer curvature comparison for the cell ending at local offset 16/4. -/
private theorem curvature_check_16 : curvatureValue 16 5292 4212 ≤ 3 := by decide +kernel

/-- The integer curvature comparison for the cell ending at local offset 20/4. -/
private theorem curvature_check_20 : curvatureValue 20 5488 4368 ≤ 4 := by decide +kernel

/-- The integer curvature comparison for the cell ending at local offset 24/4. -/
private theorem curvature_check_24 : curvatureValue 24 5684 4524 ≤ 6 := by decide +kernel

/-- The integer curvature comparison for the cell ending at local offset 25/4. -/
private theorem curvature_check_25 : curvatureValue 25 5880 4680 ≤ 2 := by decide +kernel

/-- The K156 rational residual as a function of the global log cutoff. -/
private noncomputable def k156Residual : ℝ → ℝ :=
  gaussianMidResidual (721603265 / 10 ^ 9 - 3 / 8 / gaussianDirectScale) 0 (61 / 1000)
    (middleResidualRates (49 / 20)) k156Profiles

/-- Turn a K156 integer curvature comparison and two endpoint bounds into
one lower bound for the complete closed cell. -/
private theorem k156_cell_lower {x l r m cap : ℝ} (u : ℤ) (j k : ℕ) (hu : 0 ≤ u) (hlo : 24 ≤ l)
    (hup : r - 24 = (u : ℝ) / 4) (hj : (j : ℝ) / 80 = (49 / 20) * l)
    (hk : (k : ℝ) / 80 = (39 / 20) * l) (hjp : 0 < middleTailExpDen j)
    (hkp : 0 < middleTailExpDen k) (hcap : (curvatureValue u j k : ℝ) ≤ cap) (hcap₀ : 0 ≤ cap)
    (hx : x ∈ Set.Icc l r) (hl : m ≤ k156Residual l) (hr : m ≤ k156Residual r) :
    m - cap * (r - l) ^ 2 / 8 ≤ k156Residual x := by
  let s : ℝ := 721603265 / 10 ^ 9 - 3 / 8 / gaussianDirectScale
  have hf :=
    gaussian_mid_residual_deriv s 0 (61 / 1000) (middleResidualRates (49 / 20)) k156Profiles
  have hg := gaussian_mid_residual_curv s (61 / 1000) (middleResidualRates (49 / 20)) k156Profiles
  apply
    Analysis.cell_lower_of_curvature hx hcap₀ (fun t _ ↦ (hf t).continuousAt.continuousWithinAt)
      (fun t _ ↦ hf t) (fun t _ ↦ hg t) _ hl hr
  intro t ht
  exact
    (curvature_le u j k hu (hlo.trans ht.1.le) ht.1.le ((sub_le_sub_right ht.2.le _).trans_eq hup)
          hj hk hjp hkp).trans
      hcap

/-- The six K156 cells cover the complete cutoff range, with lower bounds
strictly above the corresponding Euler-adjusted passage ceilings. -/
public theorem middle_k156_residual_gt {x : ℝ} (hx : x ∈ Set.Icc (24 : ℝ) (121 / 4)) :
    (if 29 ≤ x then -(901 / 20) else -(4407 / 100)) <
      gaussianMidResidual (721603265 / 10 ^ 9 - 3 / 8 / gaussianDirectScale) 0 (61 / 1000)
        (middleResidualRates (49 / 20))
        (middleRatProfiles (49 / 20) (7 / 2) (middleK156Scale : ℝ)
          (middleK156Profile.map (Rat.castHom ℝ))
          ((middleMomentPoly middleK156Profile (59 / 20) 0).map (Rat.castHom ℝ)))
        x := by
  change _ < k156Residual x
  obtain ⟨h0, _, h8, h12, h16, h20, h24, h25⟩ := middle_k156_residual_endpoints
  have cell8 (hc : x ∈ Set.Icc (24 : ℝ) (26)) : -44 ≤ k156Residual x := by
    have h :=
      k156_cell_lower (cap := (8 : ℝ)) (m := -40) 8 4704 3744 (by decide) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only) (by decide +kernel)
        (by decide +kernel) (by exact_mod_cast curvature_check_8) (by norm_num only) hc h0 h8
    linarith only [h]
  have cell12 (hc : x ∈ Set.Icc (26 : ℝ) (27)) : -44 ≤ k156Residual x := by
    have h :=
      k156_cell_lower (cap := (2 : ℝ)) (m := -40) 12 5096 4056 (by decide) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only) (by decide +kernel)
        (by decide +kernel) (by exact_mod_cast curvature_check_12) (by norm_num only) hc h8 h12
    linarith only [h]
  have cell16 (hc : x ∈ Set.Icc (27 : ℝ) (28)) : -44 ≤ k156Residual x := by
    have h :=
      k156_cell_lower (cap := (3 : ℝ)) (m := -40) 16 5292 4212 (by decide) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only) (by decide +kernel)
        (by decide +kernel) (by exact_mod_cast curvature_check_16) (by norm_num only) hc h12 h16
    linarith only [h]
  have cell20 (hc : x ∈ Set.Icc (28 : ℝ) (29)) : -44 ≤ k156Residual x := by
    have h :=
      k156_cell_lower (cap := (4 : ℝ)) (m := -40) 20 5488 4368 (by decide) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only) (by decide +kernel)
        (by decide +kernel) (by exact_mod_cast curvature_check_20) (by norm_num only) hc h16 h20
    linarith only [h]
  have cell24 (hc : x ∈ Set.Icc (29 : ℝ) (30)) : -(179 / 4) ≤ k156Residual x := by
    have h :=
      k156_cell_lower (cap := (6 : ℝ)) (m := -44) 24 5684 4524 (by decide) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only) (by decide +kernel)
        (by decide +kernel) (by exact_mod_cast curvature_check_24) (by norm_num only) hc
        ((by norm_num only : (-44 : ℝ) ≤ -40).trans h20) h24
    linarith only [h]
  have cell25 (hc : x ∈ Set.Icc (30 : ℝ) (121 / 4)) : -(179 / 4) ≤ k156Residual x := by
    have h :=
      k156_cell_lower (cap := (2 : ℝ)) (m := -44) 25 5880 4680 (by decide) (by norm_num only)
        (by norm_num only) (by norm_num only) (by norm_num only) (by decide +kernel)
        (by decide +kernel) (by exact_mod_cast curvature_check_25) (by norm_num only) hc h24 h25
    linarith only [h]
  by_cases h : 29 ≤ x
  · rw [ite_eq_left h]
    by_cases hh : x ≤ 30
    · linarith only [cell24 ⟨h, hh⟩]
    · linarith only [cell25 ⟨le_of_not_ge hh, hx.2⟩]
  · rw [ite_eq_right h]
    by_cases h26 : x ≤ 26
    · linarith only [cell8 ⟨hx.1, h26⟩]
    by_cases h27 : x ≤ 27
    · linarith only [cell12 ⟨le_of_not_ge h26, h27⟩]
    by_cases h28 : x ≤ 28
    · linarith only [cell16 ⟨le_of_not_ge h27, h28⟩]
    · linarith only [cell20 ⟨le_of_not_ge h28, le_of_not_ge h⟩]

/-- The K156 contradiction supplies a rejecting prime within the squared
direct cutoff for uniform triples in the second middle interval under GRH. -/
public theorem middle_k156_direct_witness
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n p q r : ℕ} [NeZero p]
    [NeZero q] [NeZero r] [NeZero n] [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)]
    [Fact (2 < q)] [Fact (2 < r)] (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hprod : n = p * q * r) (hp : Odd p) (hq : Odd q) (hr : Odd r)
    (hL : Real.log n ∈ Set.Icc (400000 : ℝ) 7000000) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (gaussianDirectScale * Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  classical
  by_contra h
  have hpass (l : ℕ) (hl : l.Prime) (hb : (l : ℝ) ≤ (gaussianDirectScale * Real.log n) ^ 2) :
    PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
    by_contra hfail
    exact h ⟨l, hl, hb, hfail⟩
  exact
    (not_lt_of_ge (middle_k156_rat_ceiling hGRH hn ho hu hprod hp hq hr hL hpass))
      (middle_k156_residual_gt (gaussian_k156_log_range hL))

end PseudoPrime.PrimeTestBounds.MillerRabin
