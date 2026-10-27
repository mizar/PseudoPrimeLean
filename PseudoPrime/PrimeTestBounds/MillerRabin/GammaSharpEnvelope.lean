/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GammaSharpComparison
public import PseudoPrime.PrimeTestBounds.MillerRabin.GammaFixedSwitch
public import PseudoPrime.PrimeTestBounds.MillerRabin.EndpointFourStep
/-! # Continuous selection for the sharper Gamma bound -/
@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A nonnegative sharper gap at an affine-radius anchor persists for all larger L
when the linear and reciprocal slope coefficients are nonnegative.
Factor the exact gap increment to prove a continuous half-line comparison. -/
theorem gammaSharpGap_affine_nonneg {L L₀ a t : ℝ} (hLL₀ : L₀ ≤ L) (ha : 0 ≤ a)
    (hr₀ : 0 < a * L₀ + t) (hslope : 0 ≤ (86733 / 98800 : ℝ) * a - 11783423 / 25000000)
    (hrecip : 0 ≤ a * (20475759 / 494000 : ℝ) - (7 / 6 : ℝ) * t)
    (hanchor : 0 ≤ gammaSharpGap L₀ (a * L₀ + t)) :
    0 ≤ gammaSharpGap L (a * L + t) := by
  let r := a * L + t
  let r₀ := a * L₀ + t
  have hdelta : 0 ≤ L - L₀ := by linarith only [hLL₀]
  have hr0 : 0 < r₀ := hr₀
  have hrEq : r = r₀ + a * (L - L₀) := by
    dsimp only [r, r₀]
    ring
  have hr : 0 < r := by
    rw [hrEq]
    exact add_pos_of_pos_of_nonneg hr0 (mul_nonneg ha hdelta)
  have hrExpr : 0 < a * L + t := by simpa only [r] using hr
  have hr0Expr : 0 < a * L₀ + t := by simpa only [r₀] using hr0
  have hid :
    gammaSharpGap L r - gammaSharpGap L₀ r₀ =
      ((86733 / 98800 : ℝ) * a - 11783423 / 25000000) * (L - L₀) +
        (a * (20475759 / 494000 : ℝ) - (7 / 6 : ℝ) * t) * (L - L₀) / (r * r₀) := by
    dsimp only [r, r₀]
    simp only [gammaSharpGap]
    field_simp [hrExpr.ne', hr0Expr.ne']
    ring_nf
  have hlinear := mul_nonneg hslope hdelta
  have hfrac : 0 ≤ (a * (20475759 / 494000 : ℝ) - (7 / 6 : ℝ) * t) * (L - L₀) / (r * r₀) := by
    apply div_nonneg
    · exact mul_nonneg hrecip hdelta
    · exact mul_nonneg hr.le hr0.le
  have hstep : 0 ≤ gammaSharpGap L r - gammaSharpGap L₀ r₀ := by
    rw [hid]
    exact add_nonneg hlinear hfrac
  change 0 ≤ gammaSharpGap L r
  have hstep' : 0 ≤ gammaSharpGap L r - gammaSharpGap L₀ (a * L₀ + t) := by
    simpa only [r₀] using hstep
  linarith only [hanchor, hstep']


/-- For 112<=L<=120, the clipped third radius is at most L-69/10.
Use H(120)<=7.2 to put the second radius above 104, then H(104)>=6.9. -/
theorem sharp_third_upper {L : ℝ} (hL : 112 ≤ L) (hU : L ≤ 120) :
    LLS.PaperStatements.endpointThirdRadius L ≤ L - 69 / 10 := by
  have h120 : LLS.PaperStatements.fullEndpointEvenGapCorrection L ≤ (36 / 5 : ℝ) :=
    (LLS.PaperStatements.fullEndpointEvenGapCorrection_strictMonoOn.monotoneOn
      (by linarith only [hL] : (8 : ℝ) ≤ L) (by norm_num only [Set.mem_Ici]) hU).trans
      LLS.PaperStatements.endpoint_correction_caps.2.2.2
  have ha : (104 : ℝ) ≤ LLS.PaperStatements.fullEndpointEvenCorrectionFirstRadius L :=
    (by linarith only [h120, hL] : (104 : ℝ) ≤
      L - LLS.PaperStatements.fullEndpointEvenGapCorrection L).trans (le_max_right _ _)
  have hb := ha.trans (LLS.PaperStatements.correction_second_gt
    (by linarith only [hL] : (45 / 4 : ℝ) ≤ L)).le
  have hcheck : LLS.PaperStatements.endpointCorrectionCheck 104 (69 / 10) 100 = true := by
    decide +kernel
  have h104 : (69 / 10 : ℝ) ≤ LLS.PaperStatements.fullEndpointEvenGapCorrection 104 := by
    simpa only [Rat.cast_ofNat, Rat.cast_div] using
      (LLS.PaperStatements.endpointCorrectionCheck_sound hcheck).1
  have hH := h104.trans (LLS.PaperStatements.fullEndpointEvenGapCorrection_strictMonoOn.monotoneOn
    (by norm_num only : (8 : ℝ) ≤ 104) (by linarith only [hb] : (8 : ℝ) ≤
      LLS.PaperStatements.fullEndpointEvenCorrectionSecondRadius L) hb)
  exact max_le (by linarith only [hL]) (by linarith only [hH])

/-- On 112<=L<=120, a correction cap at q>=third implies fourth>=L-U.
Combine the third-radius upper bound with monotonicity of the correction. -/
theorem sharp_fourth_lower {L q U : ℝ} (hL : 112 ≤ L) (hU : L ≤ 120)
    (hq : 8 ≤ q) (hcq : L - 69 / 10 ≤ q)
    (hcap : LLS.PaperStatements.fullEndpointEvenGapCorrection q ≤ U) :
    L - U ≤ LLS.PaperStatements.endpointFourthRadius L := by
  have hc : (8 : ℝ) ≤ LLS.PaperStatements.endpointThirdRadius L := le_max_left _ _
  have hH := (LLS.PaperStatements.fullEndpointEvenGapCorrection_strictMonoOn.monotoneOn
    hc hq ((sharp_third_upper hL hU).trans hcq)).trans hcap
  dsimp only [LLS.PaperStatements.endpointFourthRadius]
  linarith only [hH]

/-- For L>=100, an affine positive-gap certificate implies G1(L)<(L-U)^2.
The root is below eta*(L-U), and (99/40)*eta^2<1 supplies strictness. -/
theorem gammaSharp_lt_affine_sq {L L₀ U : ℝ} (hL : 100 ≤ L) (hlo : L₀ ≤ L)
    (hpos : 0 < L₀ - U)
    (hrecip : 0 ≤ (15891 / 25000 : ℝ) * (20475759 / 494000) +
      (7 / 6) * (15891 / 25000) * U)
    (hanchor : 0 ≤ gammaSharpGap L₀ ((15891 / 25000) * (L₀ - U))) :
    gammaSharpBound L < (L - U) ^ 2 := by
  have hLU : 0 < L - U := by linarith only [hlo, hpos]
  have hr : 0 < (15891 / 25000 : ℝ) * (L - U) :=
    mul_pos (by norm_num only) hLU
  have hg := gammaSharpGap_affine_nonneg (a := 15891 / 25000)
    (t := -(15891 / 25000) * U) hlo (by norm_num only)
    (by nlinarith only [hpos]) (by norm_num only)
    (by linarith only [hrecip]) (by convert hanchor using 1; congr 1; ring)
  have hroot := gammaSharpRoot_le_of_gap_nonneg hL hr (by convert hg using 1; congr 1; ring)
  have hs := (sq_le_sq₀ (gammaSharpRoot_pos hL).le hr.le).mpr hroot
  have hp := sq_pos_of_pos hLU
  change (99 / 40 : ℝ) * gammaSharpRoot L ^ 2 < (L - U) ^ 2
  nlinarith only [hs, hp]

/-- For 112<=L<=113, G1<C4. The anchor H(106.1)<=7 bounds the fourth radius
below by L-7; a positive affine gap controls the sharper Gamma root. -/
theorem gammaSharp_fourStep_band0 {L : ℝ} (hlo : (112 : ℝ) ≤ L)
    (hhi : L ≤ (113 : ℝ)) :
    gammaSharpBound L < LLS.PaperStatements.endpointFourStepCutoff L := by
  have hcheck : LLS.PaperStatements.endpointCorrectionCheck (1061 / 10) 0 (7) = true := by
    decide +kernel
  have hcap :
      LLS.PaperStatements.fullEndpointEvenGapCorrection (1061 / 10 : ℝ) ≤ (7 : ℝ) := by
    simpa only [Rat.cast_ofNat, Rat.cast_div] using
      (LLS.PaperStatements.endpointCorrectionCheck_sound hcheck).2
  have hlow := sharp_fourth_lower (by linarith only [hlo] : (112 : ℝ) ≤ L)
    (by linarith only [hhi]) (by norm_num only : (8 : ℝ) ≤ 1061 / 10)
    (by linarith only [hhi]) hcap
  have hsq := gammaSharp_lt_affine_sq (L₀ := 112) (U := 7)
    (by linarith only [hlo]) hlo (by norm_num only) (by norm_num only)
    (by norm_num only [gammaSharpGap])
  have hp : (0 : ℝ) ≤ L - (7) := by linarith only [hlo]
  exact hsq.trans_le ((sq_le_sq₀ hp (hp.trans hlow)).mpr hlow)

/-- For 113<=L<=120, G1<C4. The anchor H(117.2)<=3559/500 bounds the fourth
radius below by L-3559/500; a positive affine gap controls the sharper Gamma root. -/
theorem gammaSharp_fourStep_band1 {L : ℝ} (hlo : (113 : ℝ) ≤ L)
    (hhi : L ≤ (120 : ℝ)) :
    gammaSharpBound L < LLS.PaperStatements.endpointFourStepCutoff L := by
  have hcheck : LLS.PaperStatements.endpointCorrectionCheck (586 / 5) 0 (3559 / 500) = true := by
    decide +kernel
  have hcap :
      LLS.PaperStatements.fullEndpointEvenGapCorrection (586 / 5 : ℝ) ≤ (3559 / 500 : ℝ) := by
    simpa only [Rat.cast_ofNat, Rat.cast_div] using
      (LLS.PaperStatements.endpointCorrectionCheck_sound hcheck).2
  have hlow := sharp_fourth_lower (by linarith only [hlo] : (112 : ℝ) ≤ L)
    (by linarith only [hhi]) (by norm_num only : (8 : ℝ) ≤ 586 / 5)
    (by linarith only [hhi]) hcap
  have hsq := gammaSharp_lt_affine_sq (L₀ := 113) (U := 3559 / 500)
    (by linarith only [hlo]) hlo (by norm_num only) (by norm_num only)
    (by norm_num only [gammaSharpGap])
  have hp : (0 : ℝ) ≤ L - (3559 / 500) := by linarith only [hlo]
  exact hsq.trans_le ((sq_le_sq₀ hp (hp.trans hlow)).mpr hlow)

/-- For the complete continuous interval 112<=L<=120, G1 is strictly below C4.
Combine the two correction-cap bands; no numerical crossing is assumed. -/
theorem gammaSharp_lt_fourStep {L : ℝ} (hL : 112 ≤ L) (hU : L ≤ 120) :
    gammaSharpBound L < LLS.PaperStatements.endpointFourStepCutoff L := by
  by_cases h113 : L ≤ 113
  · exact gammaSharp_fourStep_band0 hL h113
  · exact gammaSharp_fourStep_band1 (le_of_not_ge h113) hU

/-- For 120<=L<=240, G1 is strictly below the 413/100-credit Gamma bound.
At the old root, its positive gap gain follows from root<=140 and the retained
reciprocal saving. Strict root and square comparisons imply the bound comparison. -/
theorem gammaSharp_lt_refined {L : ℝ} (hL : 120 ≤ L) (hU : L ≤ 240) :
    gammaSharpBound L < gamma1000RefinedBound L := by
  let r := gammaClippedPrefixRoot L (413 / 100)
  have hr0 : 0 < r := gammaClippedPrefixRoot_pos hL (by norm_num only)
  have hrU : r ≤ 140 := root140_upper hL hU (by norm_num only) (by norm_num only)
  have hz : gammaClippedPrefixGap L (413 / 100) r = 0 :=
    gammaClippedPrefixGap_root_eq_zero hL (by norm_num only)
  have hid : gammaSharpGap L r - gammaClippedPrefixGap L (413 / 100) r =
      -(87069 / 98800 - 86733 / 98800 : ℝ) * r +
      (45489517 / 11856000 - 38128717 / 11856000 : ℝ) +
      (190 / 3 - 20475759 / 494000 : ℝ) / r := by
    dsimp only [gammaSharpGap, gammaClippedPrefixGap]
    ring
  have hp1 : 0 < -(87069 / 98800 - 86733 / 98800 : ℝ) * r +
      (45489517 / 11856000 - 38128717 / 11856000 : ℝ) := by linarith only [hrU]
  have hp2 : 0 < (190 / 3 - 20475759 / 494000 : ℝ) / r :=
    div_pos (by norm_num only) hr0
  have hg : 0 < gammaSharpGap L r := by linarith only [hid, hp1, hp2, hz]
  have h100 : (100 : ℝ) ≤ L := by linarith only [hL]
  have hrle := gammaSharpRoot_le_of_gap_nonneg h100 hr0 hg.le
  have hrlt : gammaSharpRoot L < r := by
    by_contra h
    have he : gammaSharpRoot L = r := le_antisymm hrle (le_of_not_gt h)
    rw [← he, gammaSharpGap_root_eq_zero h100] at hg
    exact lt_irrefl 0 hg
  have hrad : r ≤ gammaClippedPrefixRadius L 1000 (413 / 100) := le_max_right _ _
  have hlt := hrlt.trans_le hrad
  have hs := (sq_lt_sq₀ (gammaSharpRoot_pos h100).le
    ((gammaSharpRoot_pos h100).le.trans hlt.le)).mpr hlt
  exact mul_lt_mul_of_pos_left hs (by norm_num only : (0 : ℝ) < 99 / 40)

/-- For L>=100 and positive radii, the sharper gap is strictly increasing.
Its positive linear term increases and its reciprocal penalty decreases. -/
theorem gammaSharpGap_strictMono {L r t : ℝ} (hL : 100 ≤ L) (hr : 0 < r) (hrt : r < t) :
    gammaSharpGap L r < gammaSharpGap L t := by
  have hA : 0 ≤ (7 / 6 : ℝ) * L + 20475759 / 494000 := by linarith only [hL]
  have hd := div_le_div_of_nonneg_left hA hr hrt.le
  have hm := mul_lt_mul_of_pos_left hrt (by norm_num only : (0 : ℝ) < 86733 / 98800)
  dsimp only [gammaSharpGap]
  linarith only [hd, hm]

/-- The exact switching scale S1 where G1 equals 35000.
Solve the affine gap equation at the fixed radius sqrt(1400000/99).
The certified interval is (209,210), with no rounded decimal in the definition. -/
noncomputable def gammaSharpFixedSwitch : ℝ :=
  ((86733 / 98800 : ℝ) * gammaFixedRadius - 38128717 / 11856000 -
    (20475759 / 494000) / gammaFixedRadius) /
    ((11783423 / 25000000 : ℝ) + (7 / 6) / gammaFixedRadius)

/-- The gap at the fixed 35000 radius factors as positive slope times S1-L.
Expand the switch definition and cancel its nonzero denominator. -/
theorem gammaSharpFixed_gap (L : ℝ) : gammaSharpGap L gammaFixedRadius =
    ((11783423 / 25000000 : ℝ) + (7 / 6) / gammaFixedRadius) *
      (gammaSharpFixedSwitch - L) := by
  have hD : (11783423 / 25000000 : ℝ) + (7 / 6) / gammaFixedRadius ≠ 0 :=
    ne_of_gt (add_pos (by norm_num only) (div_pos (by norm_num only) gammaFixedRadius_pos))
  rw [gammaSharpFixedSwitch, mul_sub, mul_div_cancel₀ _ hD]
  dsimp only [gammaSharpGap]
  ring

/-- The exact switching scale satisfies 209<S1<210.
Use rational gap signs at radii 118.9 and 119 and strict radius monotonicity. -/
theorem gammaSharpFixedSwitch_bounds : (209 : ℝ) < gammaSharpFixedSwitch ∧
    gammaSharpFixedSwitch < 210 := by
  have hD : 0 < (11783423 / 25000000 : ℝ) + (7 / 6) / gammaFixedRadius :=
    add_pos (by norm_num only) (div_pos (by norm_num only) gammaFixedRadius_pos)
  have hlo := gammaSharpGap_strictMono (by norm_num only : (100 : ℝ) ≤ 209)
    (by norm_num only) gammaFixedRadius_bounds.1
  have hhi := gammaSharpGap_strictMono (by norm_num only : (100 : ℝ) ≤ 210)
    gammaFixedRadius_pos gammaFixedRadius_bounds.2
  have h0 : 0 < gammaSharpGap 209 (1189 / 10) := by norm_num only [gammaSharpGap]
  have h1 : gammaSharpGap 210 119 < 0 := by norm_num only [gammaSharpGap]
  rw [gammaSharpFixed_gap] at hlo hhi
  constructor
  · nlinarith only [hlo, h0, hD]
  · nlinarith only [hhi, h1, hD]

/-- For 100<=L<=S1, G1(L)<=35000.
A nonnegative fixed-radius gap bounds the positive root, then square and rescale. -/
theorem gammaSharp_le_fixed {L : ℝ} (hL : 100 ≤ L) (hS : L ≤ gammaSharpFixedSwitch) :
    gammaSharpBound L ≤ 35000 := by
  have hg : 0 ≤ gammaSharpGap L gammaFixedRadius := by
    rw [gammaSharpFixed_gap]
    exact mul_nonneg (add_nonneg (by norm_num only)
      (div_nonneg (by norm_num only) gammaFixedRadius_pos.le)) (sub_nonneg.mpr hS)
  have hr := gammaSharpRoot_le_of_gap_nonneg hL gammaFixedRadius_pos hg
  have hs := (sq_le_sq₀ (gammaSharpRoot_pos hL).le gammaFixedRadius_pos.le).mpr hr
  have hR : gammaFixedRadius ^ 2 = (40 / 99 : ℝ) * 35000 := Real.sq_sqrt (by norm_num only)
  change (99 / 40 : ℝ) * gammaSharpRoot L ^ 2 ≤ 35000
  linarith only [hs, hR]

/-- For L>=100 with S1<=L, 35000<=G1(L).
A nonpositive fixed-radius gap and strict gap monotonicity bound the root below. -/
theorem fixed_le_gammaSharp {L : ℝ} (hL : 100 ≤ L) (hS : gammaSharpFixedSwitch ≤ L) :
    (35000 : ℝ) ≤ gammaSharpBound L := by
  have hg : gammaSharpGap L gammaFixedRadius ≤ 0 := by
    rw [gammaSharpFixed_gap]
    exact mul_nonpos_of_nonneg_of_nonpos (add_nonneg (by norm_num only)
      (div_nonneg (by norm_num only) gammaFixedRadius_pos.le)) (sub_nonpos.mpr hS)
  have hr : gammaFixedRadius ≤ gammaSharpRoot L := by
    by_contra h
    have hm := gammaSharpGap_strictMono hL (gammaSharpRoot_pos hL) (lt_of_not_ge h)
    rw [gammaSharpGap_root_eq_zero hL] at hm
    linarith only [hm, hg]
  have hs := (sq_le_sq₀ gammaFixedRadius_pos.le (gammaSharpRoot_pos hL).le).mpr hr
  have hR : gammaFixedRadius ^ 2 = (40 / 99 : ℝ) * 35000 := Real.sq_sqrt (by norm_num only)
  change (35000 : ℝ) ≤ (99 / 40 : ℝ) * gammaSharpRoot L ^ 2
  linarith only [hs, hR]

/-- At the exact switch S1, G1 equals 35000.
Apply the two one-sided inequalities and antisymmetry. -/
theorem gammaSharp_at_switch : gammaSharpBound gammaSharpFixedSwitch = 35000 := by
  have hL : (100 : ℝ) ≤ gammaSharpFixedSwitch := by
    linarith only [gammaSharpFixedSwitch_bounds.1]
  exact le_antisymm (gammaSharp_le_fixed hL le_rfl) (fixed_le_gammaSharp hL le_rfl)

/-- For 100<=L<S1, G1(L)<35000.
The fixed-radius gap is strictly positive, so the root is strictly smaller.
This proves the improvement over the fixed branch up to the exact crossing. -/
theorem gammaSharp_lt_fixed {L : ℝ} (hL : 100 ≤ L) (hS : L < gammaSharpFixedSwitch) :
    gammaSharpBound L < 35000 := by
  have hg : 0 < gammaSharpGap L gammaFixedRadius := by
    rw [gammaSharpFixed_gap]
    exact mul_pos (add_pos (by norm_num only)
      (div_pos (by norm_num only) gammaFixedRadius_pos)) (sub_pos.mpr hS)
  have hrle := gammaSharpRoot_le_of_gap_nonneg hL gammaFixedRadius_pos hg.le
  have hrlt : gammaSharpRoot L < gammaFixedRadius := by
    by_contra h
    have he := le_antisymm hrle (le_of_not_gt h)
    rw [← he, gammaSharpGap_root_eq_zero hL] at hg
    exact lt_irrefl 0 hg
  have hs := (sq_lt_sq₀ (gammaSharpRoot_pos hL).le gammaFixedRadius_pos.le).mpr hrlt
  have hR : gammaFixedRadius ^ 2 = (40 / 99 : ℝ) * 35000 := Real.sq_sqrt (by norm_num only)
  change (99 / 40 : ℝ) * gammaSharpRoot L ^ 2 < 35000
  linarith only [hs, hR]

end PseudoPrime.PrimeTestBounds.MillerRabin
