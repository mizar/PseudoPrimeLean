/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianRecoveredRoot

/-! # Low-floor Gaussian budgets -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The Gaussian root with floor u and residual D. Positive budget parameters
supply the large-index radius, while the floor fixes the tail domain. -/
noncomputable def gaussianLowRoot (u D L : ℝ) : ℝ :=
  max u
    (gaussianBudgetRoot gaussianMRRefinedD gaussianMRRefinedBeta
      (gaussianMRRefinedConductor * L + D))

/-- The squared floored root, used as the radius whose square is the Mellin scale. -/
noncomputable def gaussianLowRadius (u D L : ℝ) : ℝ :=
  gaussianLowRoot u D L ^ 2

/-- Six fifths of the squared radius is the prime-witness cutoff for a profile. -/
noncomputable def gaussianLowBound (u D L : ℝ) : ℝ :=
  (6 / 5 : ℝ) * gaussianLowRadius u D L ^ 2

/-- Every floored root is at least its floor, independently of the budget. -/
theorem gaussianLow_root_floor (u D L : ℝ) : u ≤ gaussianLowRoot u D L :=
  le_max_left _ _

/-- For a floor at least nine and nonnegative residual and L, the root
satisfies the large-index quadratic budget. Increasing the raw root to its floor
preserves the inequality by the quadratic root comparison. -/
theorem gaussianLow_budget {u D L : ℝ} (hu : 9 ≤ u) (hD : 0 ≤ D) (hL : 0 ≤ L) :
    gaussianMRRefinedConductor * L + gaussianMRRefinedBeta * gaussianLowRoot u D L + D ≤
      gaussianMRRefinedD * gaussianLowRadius u D L := by
  have hs : 9 ≤ gaussianLowRoot u D L := hu.trans (le_max_left _ _)
  have hc : 0 ≤ gaussianMRRefinedConductor := by norm_num only [gaussianMRRefinedConductor]
  have hb : gaussianMRRefinedBeta < 9 * gaussianMRRefinedD := by
    norm_num only [gaussianMRRefinedD, gaussianMRRefinedBeta, gaussianMRRefinedMass,
      gaussianMRRefinedWidth, gaussianMR6FifthsIndex, gaussianMR6FifthsEndpoint]
  have hcoef : gaussianMRRefinedBeta < gaussianMRRefinedD * gaussianLowRoot u D L := by
    have hm := mul_le_mul_of_nonneg_left hs gaussianMRRefined_coefficients.1.le
    linarith only [hb, hm]
  have he :=
    gaussianBudget_of_root_le gaussianMRRefined_coefficients.1 gaussianMRRefined_coefficients.2
      (add_nonneg (mul_nonneg hc hL) hD) hcoef
      (show
        gaussianBudgetRoot gaussianMRRefinedD gaussianMRRefinedBeta
            (gaussianMRRefinedConductor * L + D) ≤
          gaussianLowRoot u D L
        from le_max_right _ _)
  change _ ≤ gaussianMRRefinedD * gaussianLowRadius u D L at he
  linarith only [he]

/-- Every fixed floor and residual define a monotone root as L increases. -/
theorem gaussianLow_root_mono {u D : ℝ} : Monotone (gaussianLowRoot u D) := by
  intro L K hLK
  apply max_le_max (le_refl u)
  apply gaussianBudgetRoot_mono gaussianMRRefined_coefficients.1
  exact
    add_le_add
      (mul_le_mul_of_nonneg_left hLK
        (by norm_num only [gaussianMRRefinedConductor] : 0 ≤ gaussianMRRefinedConductor))
      (le_refl D)

/-- A rational scale certificate at positive R0 controls both Gaussian tail
terms for every larger radius. Monotonicity of reciprocal powers gives the
continuous estimate used by the five low-floor tail certificates. -/
theorem gaussianLow_tail {R R0 q T : ℝ} (hR0 : 0 < R0) (hR : R0 ≤ R) (hq : 0 < q)
    (hpower : q ^ 16 ≤ R0 ^ 2) (hcap : (473 / 10 : ℝ) / (q * R0) + (512 / 27 : ℝ) / R0 ^ 2 ≤ T) :
    (473 / 10 : ℝ) * (R ^ 2) ^ (-9 / 16 : ℝ) + (512 / 27 : ℝ) / R ^ 2 ≤ T := by
  have hp : 0 < R := hR0.trans_le hR
  have hsq := (sq_le_sq₀ hR0.le hp.le).mpr hR
  have hdec := LLS.PaperStatements.rpow_neg_nine_sixteenths_le_div_scale_sqrt hq (hpower.trans hsq)
  rw [Real.sqrt_sq hp.le] at hdec
  have hl := mul_le_mul_of_nonneg_left hdec (by norm_num only : (0 : ℝ) ≤ 473 / 10)
  have ha :=
    div_le_div_of_nonneg_left (by norm_num only : (0 : ℝ) ≤ 473 / 10) (mul_pos hq hR0)
      (mul_le_mul_of_nonneg_left hR hq.le)
  have hb :=
    div_le_div_of_nonneg_left (by norm_num only : (0 : ℝ) ≤ 512 / 27) (sq_pos_of_pos hR0) hsq
  have hid : (473 / 10 : ℝ) * (1 / (q * R)) = (473 / 10 : ℝ) / (q * R) := by ring
  rw [hid] at hl
  linarith only [hl, ha, hb, hcap]

/-- The low rational radius anchor gives the certified continuous tail cap. -/
theorem gaussianLow_tail_low {r : ℝ} (hr : (91 / 10 : ℝ) ^ 2 ≤ r) :
    (473 / 10 : ℝ) * (r ^ 2) ^ (-9 / 16 : ℝ) + (512 / 27 : ℝ) / r ^ 2 ≤ 333 / 1000 := by
  exact
    gaussianLow_tail (R0 := (91 / 10 : ℝ) ^ 2) (q := 173 / 100) (by norm_num only) hr
      (by norm_num only) (by norm_num only) (by norm_num only)

/-- The middle rational radius anchor gives the certified continuous tail cap. -/
theorem gaussianLow_tail_middle {r : ℝ} (hr : (19 / 2 : ℝ) ^ 2 ≤ r) :
    (473 / 10 : ℝ) * (r ^ 2) ^ (-9 / 16 : ℝ) + (512 / 27 : ℝ) / r ^ 2 ≤ 301 / 1000 := by
  exact
    gaussianLow_tail (R0 := (19 / 2 : ℝ) ^ 2) (q := 351 / 200) (by norm_num only) hr
      (by norm_num only) (by norm_num only) (by norm_num only)

/-- The upper rational radius anchor gives the certified continuous tail cap. -/
theorem gaussianLow_tail_upper {r : ℝ} (hr : (49 / 5 : ℝ) ^ 2 ≤ r) :
    (473 / 10 : ℝ) * (r ^ 2) ^ (-9 / 16 : ℝ) + (512 / 27 : ℝ) / r ^ 2 ≤ 281 / 1000 := by
  exact
    gaussianLow_tail (R0 := (49 / 5 : ℝ) ^ 2) (q := 53 / 30) (by norm_num only) hr
      (by norm_num only) (by norm_num only) (by norm_num only)

/-- The four_low rational radius anchor gives the certified continuous tail cap. -/
theorem gaussianLow_tail_four_low {r : ℝ} (hr : (7559 / 10000 : ℝ) * (91 / 10) ^ 2 ≤ r) :
    (473 / 10 : ℝ) * (r ^ 2) ^ (-9 / 16 : ℝ) + (512 / 27 : ℝ) / r ^ 2 ≤ 458 / 1000 := by
  exact
    gaussianLow_tail (R0 := (7559 / 10000 : ℝ) * (91 / 10) ^ 2) (q := 167 / 100) (by norm_num only)
      hr (by norm_num only) (by norm_num only) (by norm_num only)

/-- The four_upper rational radius anchor gives the certified continuous tail cap. -/
theorem gaussianLow_tail_four_upper {r : ℝ} (hr : (7559 / 10000 : ℝ) * (19 / 2) ^ 2 ≤ r) :
    (473 / 10 : ℝ) * (r ^ 2) ^ (-9 / 16 : ℝ) + (512 / 27 : ℝ) / r ^ 2 ≤ 415 / 1000 := by
  exact
    gaussianLow_tail (R0 := (7559 / 10000 : ℝ) * (19 / 2) ^ 2) (q := 169 / 100) (by norm_num only)
      hr (by norm_num only) (by norm_num only) (by norm_num only)

end PseudoPrime.Analysis
