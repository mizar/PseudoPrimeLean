/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleCurvatureCheck
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK141LowerCharge
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleTailBudget
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleResidualProfile

/-! # K141 direct residual endpoint bounds -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The two K141 rational profiles share the coefficient translation at 20. -/
private def costRows : MiddleIntRow × MiddleIntRow :=
  middleInputRows BData 31 20 5 3 2 middleK141Scale

/-- Both K141 integer rows have positive common denominators. -/
private theorem cost_rows_pos : 0 < costRows.1.den ∧ 0 < costRows.2.den := by
  exact middle_input_rows_pos BData 31 20 5 3 2 middleK141Scale (by decide) (by decide) (by decide)

/-- The K141 endpoint residue computed at local offset `u / 2`. -/
private def endpointValue (u : ℤ) (j k l : ℕ) : ℚ :=
  middleEndpointLower (7215924929 / 10 ^ 10 - 3 / 8 / (519674416 / 10 ^ 9)) (61 / 1000)
    ((u : ℚ) / 2 + 20) (middleRowUpper costRows.1 31 u 2) (middleRowUpper costRows.2 31 u 2) j k l

/-- The rational K141 endpoint computation transfers to its analytic residual. -/
private theorem endpoint_le (u : ℤ) (j k l : ℕ) (hj : (j : ℝ) / 80 = ((u : ℝ) / 2 + 20) / 2)
    (hk : (k : ℝ) / 80 = 2 * ((u : ℝ) / 2 + 20))
    (hl : (l : ℝ) / 80 = (2 - 1 / 2) * ((u : ℝ) / 2 + 20)) (hkp : 0 < middleTailExpDen k)
    (hlp : 0 < middleTailExpDen l) :
    (endpointValue u j k l : ℝ) ≤
      gaussianMidResidual (7215924929 / 10 ^ 10 - 3 / 8 / gaussianDirectScale) 0 (61 / 1000)
        (middleResidualRates 2)
        (middleRatProfiles 2 (7 / 2) (middleK141Scale : ℝ) (middleK141Profile.map (Rat.castHom ℝ))
          ((middleMomentPoly middleK141Profile (5 / 2) 0).map (Rat.castHom ℝ)))
        ((u : ℝ) / 2 + 20) := by
  have hi :=
    middle_input_rows_eval BData 31 20 5 3 2 middleK141Scale (by decide) (by decide) (by decide)
      (by decide) ((u : ℝ) / 2)
  norm_num only [Rat.cast_add, Rat.cast_div, Rat.cast_ofNat] at hi
  have hu := middle_row_upper_le costRows.1 31 u 2 cost_rows_pos.1 (by decide) hi.1
  have hv := middle_row_upper_le costRows.2 31 u 2 cost_rows_pos.2 (by decide) hi.2
  have hU : 0 ≤ middleRowUpper costRows.1 31 u 2 :=
    div_nonneg (Int.cast_nonneg_iff.mpr (le_max_left _ _))
      (Int.cast_nonneg_iff.mpr cost_rows_pos.1.le)
  have hV : 0 ≤ middleRowUpper costRows.2 31 u 2 :=
    div_nonneg (Int.cast_nonneg_iff.mpr (le_max_left _ _))
      (Int.cast_nonneg_iff.mpr cost_rows_pos.2.le)
  have hx : (((u : ℚ) / 2 + 20 : ℚ) : ℝ) = (u : ℝ) / 2 + 20 := by
    simp only [Rat.cast_add, Rat.cast_div, Rat.cast_intCast, Rat.cast_ofNat]
  have h :=
    middle_endpoint_lower_le (7215924929 / 10 ^ 10 - 3 / 8 / (519674416 / 10 ^ 9)) (61 / 1000)
      ((u : ℚ) / 2 + 20) _ _ 2 _ j k l (by decide +kernel) hU hV (hx ▸ hj) (hx ▸ hk) (hx ▸ hl) hkp
      hlp (hx ▸ hu) (hx ▸ hv)
  simpa only [endpointValue, hx, Rat.cast_sub, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat,
    gaussianDirectScale, middleK141Profile] using h

/-- The three outward K141 endpoint comparisons have a common lower bound. -/
private theorem endpoint_checks :
    (-18 : ℚ) ≤ endpointValue 0 800 3200 2400 ∧
      (-18 : ℚ) ≤ endpointValue 5 900 3600 2700 ∧ (-18 : ℚ) ≤ endpointValue 10 1000 4000 3000 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

/-- The K141 residual is at least minus eighteen at all three cell endpoints. -/
public theorem middle_k141_residual_endpoints :
    let F :=
      gaussianMidResidual (7215924929 / 10 ^ 10 - 3 / 8 / gaussianDirectScale) 0 (61 / 1000)
        (middleResidualRates 2)
        (middleRatProfiles 2 (7 / 2) (middleK141Scale : ℝ) (middleK141Profile.map (Rat.castHom ℝ))
          ((middleMomentPoly middleK141Profile (5 / 2) 0).map (Rat.castHom ℝ)))
    (-18 : ℝ) ≤ F 20 ∧ (-18 : ℝ) ≤ F (45 / 2) ∧ (-18 : ℝ) ≤ F 25 := by
  intro F
  have h₀ :=
    endpoint_le 0 800 3200 2400 (by norm_num only) (by norm_num only) (by norm_num only)
      (by decide +kernel) (by decide +kernel)
  have h₁ :=
    endpoint_le 5 900 3600 2700 (by norm_num only) (by norm_num only) (by norm_num only)
      (by decide +kernel) (by decide +kernel)
  have h₂ :=
    endpoint_le 10 1000 4000 3000 (by norm_num only) (by norm_num only) (by norm_num only)
      (by decide +kernel) (by decide +kernel)
  have hc₀ := (Rat.cast_le (K := ℝ)).mpr endpoint_checks.1
  have hc₁ := (Rat.cast_le (K := ℝ)).mpr endpoint_checks.2.1
  have hc₂ := (Rat.cast_le (K := ℝ)).mpr endpoint_checks.2.2
  norm_num only [Rat.cast_neg, Rat.cast_ofNat, Int.cast_ofNat,
    Int.cast_zero] at hc₀ hc₁ hc₂ h₀ h₁ h₂
  dsimp only [F]
  norm_num only
  exact ⟨hc₀.trans h₀, hc₁.trans h₁, hc₂.trans h₂⟩

/-- The K141 rational decay profiles used in its derivative checks. -/
private noncomputable def k141Profiles : Fin 2 → Polynomial ℝ :=
  middleRatProfiles 2 (7 / 2) (middleK141Scale : ℝ) (middleK141Profile.map (Rat.castHom ℝ))
    ((middleMomentPoly middleK141Profile (5 / 2) 0).map (Rat.castHom ℝ))

/-- Total curvature cap at the right local offset, using the left grid indices. -/
private def curvatureValue (u : ℤ) (j k : ℕ) : ℚ :=
  middleCurvUpper costRows.1 31 4 2 u 2 / middleTailExpDen j +
    middleCurvUpper costRows.2 31 3 2 u 2 / middleTailExpDen k

/-- Transfer the K141 integer comparisons to the signed residual curvature. -/
private theorem curvature_le {x l : ℝ} (u : ℤ) (j k : ℕ) (hu : 0 ≤ u) (hx : 20 ≤ x) (hl : l ≤ x)
    (hxu : x - 20 ≤ (u : ℝ) / 2) (hj : (j : ℝ) / 80 = 2 * l) (hk : (k : ℝ) / 80 = (3 / 2) * l)
    (hjp : 0 < middleTailExpDen j) (hkp : 0 < middleTailExpDen k) :
    gaussianMidResidualCurv (7215924929 / 10 ^ 10 - 3 / 8 / gaussianDirectScale) (61 / 1000)
        (middleResidualRates 2) k141Profiles x ≤
      (curvatureValue u j k : ℝ) := by
  have hrow (t : ℝ) :=
    middle_input_rows_eval BData 31 20 5 3 2 middleK141Scale (by decide) (by decide) (by decide)
      (by decide) t
  norm_num only [Rat.cast_add, Rat.cast_div, Rat.cast_ofNat] at hrow
  have hrow₀ (t : ℝ) :
    ((costRows.1.poly 31).map (Rat.castHom ℝ)).eval t = (k141Profiles 0).eval (t + 20) := by
    simpa only [k141Profiles, middleK141Profile, costRows] using (hrow t).1
  have hrow₁ (t : ℝ) :
    ((costRows.2.poly 31).map (Rat.castHom ℝ)).eval t = (k141Profiles 1).eval (t + 20) := by
    simpa only [k141Profiles, middleK141Profile, costRows] using (hrow t).2
  have hl' : l ≤ x - 20 + 20 := by rwa [sub_add_cancel]
  have ht := sub_nonneg.mpr hx
  have h₀ :=
    middle_row_decay_curv_le costRows.1 31 4 2 u 2 j cost_rows_pos.1 (by decide) (by decide) hu
      (by decide) ht hxu hl'
      (by simpa only [Int.cast_ofNat, show (4 / 2 : ℝ) = 2 by norm_num only] using hj) hjp hrow₀
  have h₁ :=
    middle_row_decay_curv_le costRows.2 31 3 2 u 2 k cost_rows_pos.2 (by decide) (by decide) hu
      (by decide) ht hxu hl' (by simpa only [Int.cast_ofNat] using hk) hkp hrow₁
  have h :=
    gaussian_mid_curv_le_decay
      (show 7215924929 / 10 ^ 10 - 3 / 8 / gaussianDirectScale ≤ 0 by
        norm_num only [gaussianDirectScale])
      (by norm_num only : (0 : ℝ) ≤ 61 / 1000) (middleResidualRates 2) k141Profiles x
  have er : middleResidualRates 2 1 = (3 / 2 : ℝ) := by
    change 2 - 1 / 2 = (3 / 2 : ℝ)
    norm_num only
  rw [gaussianDecaySum, Fin.sum_univ_two, er] at h
  simp only [middleResidualRates, Fin.cases_zero] at h
  simp only [sub_add_cancel, Int.cast_ofNat, show (4 / 2 : ℝ) = 2 by norm_num only] at h₀ h₁
  rw [curvatureValue, Rat.cast_add]
  linarith only [h, h₀, h₁]

/-- The two K141 cells each have signed curvature at most two. -/
private theorem curvature_checks :
    curvatureValue 5 3200 2400 ≤ 2 ∧ curvatureValue 10 3600 2700 ≤ 2 := by
  constructor <;> decide +kernel

/-- Both K141 cells have residual at least minus twenty, with their common
endpoint lower bound and a curvature loss of at most (25/16). -/
public theorem middle_k141_residual_ge {x : ℝ} (hx : x ∈ Set.Icc (20 : ℝ) 25) :
    -20 ≤
      gaussianMidResidual (7215924929 / 10 ^ 10 - 3 / 8 / gaussianDirectScale) 0 (61 / 1000)
        (middleResidualRates 2)
        (middleRatProfiles 2 (7 / 2) (middleK141Scale : ℝ) (middleK141Profile.map (Rat.castHom ℝ))
          ((middleMomentPoly middleK141Profile (5 / 2) 0).map (Rat.castHom ℝ)))
        x := by
  let s : ℝ := 7215924929 / 10 ^ 10 - 3 / 8 / gaussianDirectScale
  let f := gaussianMidResidual s 0 (61 / 1000) (middleResidualRates 2) k141Profiles
  have hf := gaussian_mid_residual_deriv s 0 (61 / 1000) (middleResidualRates 2) k141Profiles
  have hg := gaussian_mid_residual_curv s (61 / 1000) (middleResidualRates 2) k141Profiles
  have hc {l r : ℝ} : ContinuousOn f (Set.Icc l r) := fun t _ ↦
    (hf t).continuousAt.continuousWithinAt
  obtain ⟨h₀, h₁, h₂⟩ := middle_k141_residual_endpoints
  have hb₀ : (curvatureValue 5 3200 2400 : ℝ) ≤ 2 := by exact_mod_cast curvature_checks.1
  have hb₁ : (curvatureValue 10 3600 2700 : ℝ) ≤ 2 := by exact_mod_cast curvature_checks.2
  change -20 ≤ f x
  by_cases h : x ≤ 45 / 2
  · have hcurv (t : ℝ) (ht : t ∈ Set.Ioo (20 : ℝ) (45 / 2)) := by
      exact
        (curvature_le 5 3200 2400 (by decide) ht.1.le ht.1.le
              (by
                norm_num only [Int.cast_ofNat]; linarith only [ht.2])
              (by norm_num only) (by norm_num only) (by decide +kernel) (by decide +kernel)).trans
          hb₀
    have he :=
      Analysis.cell_lower_of_curvature ⟨hx.1, h⟩ (by norm_num only : (0 : ℝ) ≤ 2) hc
        (fun t _ ↦ hf t) (fun t _ ↦ hg t) hcurv h₀ h₁
    linarith only [he]
  · have hcurv (t : ℝ) (ht : t ∈ Set.Ioo (45 / 2 : ℝ) 25) := by
      exact
        (curvature_le 10 3600 2700 (by decide)
              ((by norm_num only : (20 : ℝ) ≤ 45 / 2).trans ht.1.le) ht.1.le
              (by
                norm_num only [Int.cast_ofNat]; linarith only [ht.2])
              (by norm_num only) (by norm_num only) (by decide +kernel) (by decide +kernel)).trans
          hb₁
    have he :=
      Analysis.cell_lower_of_curvature ⟨le_of_not_ge h, hx.2⟩ (by norm_num only : (0 : ℝ) ≤ 2) hc
        (fun t _ ↦ hf t) (fun t _ ↦ hg t) hcurv h₁ h₂
    linarith only [he]

/-- A uniform Korselt triple in the K141 logarithmic input interval has a
rejecting prime at most the squared direct cutoff under GRH. -/
public theorem middle_k141_direct_witness
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n p q r : ℕ} [NeZero p]
    [NeZero q] [NeZero r] [NeZero n] [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)]
    [Fact (2 < q)] [Fact (2 < r)] (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hprod : n = p * q * r) (hp : Odd p) (hq : Odd q) (hr : Odd r)
    (hL : Real.log n ∈ Set.Icc (42410 : ℝ) 400000) :
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
  have hlo := middle_k141_residual_ge (gaussian_k141_log_range hL)
  have hup := middle_k141_rat_ceiling hGRH hn ho hu hprod hp hq hr hL hpass
  linarith only [hlo, hup]

end PseudoPrime.PrimeTestBounds.MillerRabin
