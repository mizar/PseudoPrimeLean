/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GammaReflectedComparison
public import PseudoPrime.PrimeTestBounds.MillerRabin.ImprovedIntervalSelection

/-! # Continuous comparisons and exact switch for the reflected Gamma bound -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For L>=100, the reflected Gamma bound is strictly below G1. Its gap
gain at the G1 root is 55079/(3600r)>0, forcing a strictly smaller root
and hence a strictly smaller cutoff. -/
theorem gammaReflected_lt_sharp {L : ℝ} (hL : 100 ≤ L) :
    gammaReflectedBound L < gammaSharpBound L := by
  let r := gammaSharpRoot L
  have hr : 0 < r := gammaSharpRoot_pos hL
  have he : gammaSharpGap L r = 0 := gammaSharpGap_root_eq_zero hL
  have hid : gammaReflectedGap L r - gammaSharpGap L r = (55079 / 3600 : ℝ) / r := by
    dsimp only [gammaReflectedGap, gammaSharpGap]
    ring
  have hpos := div_pos (by norm_num only : (0 : ℝ) < 55079 / 3600) hr
  have hg : 0 < gammaReflectedGap L r := by linarith only [hid, he, hpos]
  have hle := gammaReflectedRoot_le_of_gap_nonneg hL hr hg.le
  have hlt : gammaReflectedRoot L < r := by
    by_contra hn
    have heq := le_antisymm hle (le_of_not_gt hn)
    rw [← heq, gammaReflectedGap_root_eq_zero hL] at hg
    exact lt_irrefl 0 hg
  have hs := (sq_lt_sq₀ (gammaReflectedRoot_pos hL).le hr.le).mpr hlt
  exact mul_lt_mul_of_pos_left hs (by norm_num only : (0 : ℝ) < 99 / 40)

/-- A nonnegative reflected gap at a positive affine-radius anchor persists
for larger L when both increment coefficients are nonnegative. Factor
the exact affine and reciprocal increments to certify continuous comparisons. -/
theorem gammaReflectedGap_affine_nonneg {L L₀ a t : ℝ} (hLL₀ : L₀ ≤ L) (ha : 0 ≤ a)
    (hr₀ : 0 < a * L₀ + t) (hslope : 0 ≤ (86733 / 98800 : ℝ) * a - 11783423 / 25000000)
    (hrecip : 0 ≤ a * (58129633 / 2223000 : ℝ) - (7 / 6 : ℝ) * t)
    (hanchor : 0 ≤ gammaReflectedGap L₀ (a * L₀ + t)) : 0 ≤ gammaReflectedGap L (a * L + t) := by
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
    gammaReflectedGap L r - gammaReflectedGap L₀ r₀ =
      ((86733 / 98800 : ℝ) * a - 11783423 / 25000000) * (L - L₀) +
        (a * (58129633 / 2223000 : ℝ) - (7 / 6 : ℝ) * t) * (L - L₀) / (r * r₀) := by
    dsimp only [r, r₀]
    simp only [gammaReflectedGap]
    field_simp [hrExpr.ne', hr0Expr.ne']
    ring_nf
  have hlinear := mul_nonneg hslope hdelta
  have hfrac : 0 ≤ (a * (58129633 / 2223000 : ℝ) - (7 / 6 : ℝ) * t) * (L - L₀) / (r * r₀) := by
    apply div_nonneg
    · exact mul_nonneg hrecip hdelta
    · exact mul_nonneg hr.le hr0.le
  have hstep : 0 ≤ gammaReflectedGap L r - gammaReflectedGap L₀ r₀ := by
    rw [hid]
    exact add_nonneg hlinear hfrac
  change 0 ≤ gammaReflectedGap L r
  have hstep' : 0 ≤ gammaReflectedGap L r - gammaReflectedGap L₀ (a * L₀ + t) := by
    simpa only [r₀] using hstep
  linarith only [hanchor, hstep']

/-- For L>=100, an affine reflected-gap certificate bounds G2 strictly
below (L-U) squared. The rational factor eta=15891/25000 has
(99/40) eta squared<1, supplying strictness after the root comparison. -/
theorem gammaReflected_lt_affine_sq {L L₀ U : ℝ} (hL : 100 ≤ L) (hlo : L₀ ≤ L) (hpos : 0 < L₀ - U)
    (hrecip : 0 ≤ (15891 / 25000 : ℝ) * (58129633 / 2223000) + (7 / 6) * (15891 / 25000) * U)
    (hanchor : 0 ≤ gammaReflectedGap L₀ ((15891 / 25000) * (L₀ - U))) :
    gammaReflectedBound L < (L - U) ^ 2 := by
  have hLU : 0 < L - U := by linarith only [hlo, hpos]
  have hr : 0 < (15891 / 25000 : ℝ) * (L - U) := mul_pos (by norm_num only) hLU
  have hg :=
    gammaReflectedGap_affine_nonneg (a := 15891 / 25000) (t := -(15891 / 25000) * U) hlo
      (by norm_num only) (by nlinarith only [hpos]) (by norm_num only) (by linarith only [hrecip])
      (by
        convert hanchor using 1; congr 1; ring)
  have hroot :=
    gammaReflectedRoot_le_of_gap_nonneg hL hr
      (by
        convert hg using 1; congr 1; ring)
  have hs := (sq_le_sq₀ (gammaReflectedRoot_pos hL).le hr.le).mpr hroot
  have hp := sq_pos_of_pos hLU
  change (99 / 40 : ℝ) * gammaReflectedRoot L ^ 2 < (L - U) ^ 2
  nlinarith only [hs, hp]

/-- For L>=100 and positive radii, the reflected gap strictly increases
with the radius. Its positive linear term increases and the reciprocal
penalty decreases. This controls exact switching inequalities. -/
theorem gammaReflectedGap_strictMono {L r t : ℝ} (hL : 100 ≤ L) (hr : 0 < r) (hrt : r < t) :
    gammaReflectedGap L r < gammaReflectedGap L t := by
  have hA : 0 ≤ (7 / 6 : ℝ) * L + 58129633 / 2223000 := by linarith only [hL]
  have hd := div_le_div_of_nonneg_left hA hr hrt.le
  have hm := mul_lt_mul_of_pos_left hrt (by norm_num only : (0 : ℝ) < 86733 / 98800)
  dsimp only [gammaReflectedGap]
  linarith only [hd, hm]

/-- The exact scale S2 where the reflected cutoff equals 35000. Solve
the fixed-radius gap at sqrt(1400000/99); no decimal approximation
is used as a branch boundary. -/
noncomputable def gammaReflectedFixedSwitch : ℝ :=
  ((86733 / 98800 : ℝ) * gammaFixedRadius - 38128717 / 11856000 -
      (58129633 / 2223000) / gammaFixedRadius) /
    ((11783423 / 25000000 : ℝ) + (7 / 6) / gammaFixedRadius)

/-- At the fixed 35000 radius, the reflected gap equals a positive
slope times S2-L. Expand the exact switch and cancel its denominator. -/
theorem gammaReflectedFixed_gap (L : ℝ) :
    gammaReflectedGap L gammaFixedRadius =
      ((11783423 / 25000000 : ℝ) + (7 / 6) / gammaFixedRadius) *
        (gammaReflectedFixedSwitch - L) := by
  have hD : (11783423 / 25000000 : ℝ) + (7 / 6) / gammaFixedRadius ≠ 0 :=
    ne_of_gt (add_pos (by norm_num only) (div_pos (by norm_num only) gammaFixedRadius_pos))
  rw [gammaReflectedFixedSwitch, mul_sub, mul_div_cancel₀ _ hD]
  dsimp only [gammaReflectedGap]
  ring

/-- The exact reflected switch lies between 209 and 210. Rational gap
signs at positive radius brackets and strict monotonicity certify the enclosure. -/
theorem gammaReflectedFixedSwitch_bounds :
    (209 : ℝ) < gammaReflectedFixedSwitch ∧ gammaReflectedFixedSwitch < 210 := by
  have hD : 0 < (11783423 / 25000000 : ℝ) + (7 / 6) / gammaFixedRadius :=
    add_pos (by norm_num only) (div_pos (by norm_num only) gammaFixedRadius_pos)
  have hlo :=
    gammaReflectedGap_strictMono (by norm_num only : (100 : ℝ) ≤ 209) (by norm_num only)
      gammaFixedRadius_bounds.1
  have hhi :=
    gammaReflectedGap_strictMono (by norm_num only : (100 : ℝ) ≤ 210) gammaFixedRadius_pos
      gammaFixedRadius_bounds.2
  have h0 : 0 < gammaReflectedGap 209 (1189 / 10) := by norm_num only [gammaReflectedGap]
  have h1 : gammaReflectedGap 210 119 < 0 := by norm_num only [gammaReflectedGap]
  rw [gammaReflectedFixed_gap] at hlo hhi
  constructor
  · nlinarith only [hlo, h0, hD]
  · nlinarith only [hhi, h1, hD]

/-- For 100<=L<=S2, G2(L)<=35000. Its nonnegative gap at the fixed
radius bounds the positive root, which may then be squared and rescaled. -/
theorem gammaReflected_le_fixed {L : ℝ} (hL : 100 ≤ L) (hS : L ≤ gammaReflectedFixedSwitch) :
    gammaReflectedBound L ≤ 35000 := by
  have hg : 0 ≤ gammaReflectedGap L gammaFixedRadius := by
    rw [gammaReflectedFixed_gap]
    exact
      mul_nonneg
        (add_nonneg (by norm_num only) (div_nonneg (by norm_num only) gammaFixedRadius_pos.le))
        (sub_nonneg.mpr hS)
  have hr := gammaReflectedRoot_le_of_gap_nonneg hL gammaFixedRadius_pos hg
  have hs := (sq_le_sq₀ (gammaReflectedRoot_pos hL).le gammaFixedRadius_pos.le).mpr hr
  have hR : gammaFixedRadius ^ 2 = (40 / 99 : ℝ) * 35000 := Real.sq_sqrt (by norm_num only)
  change (99 / 40 : ℝ) * gammaReflectedRoot L ^ 2 ≤ 35000
  linarith only [hs, hR]

/-- For L>=100 with S2<=L, 35000<=G2(L). The nonpositive fixed-radius
gap and strict radius monotonicity bound the root below by the fixed radius. -/
theorem fixed_le_gammaReflected {L : ℝ} (hL : 100 ≤ L) (hS : gammaReflectedFixedSwitch ≤ L) :
    (35000 : ℝ) ≤ gammaReflectedBound L := by
  have hg : gammaReflectedGap L gammaFixedRadius ≤ 0 := by
    rw [gammaReflectedFixed_gap]
    exact
      mul_nonpos_of_nonneg_of_nonpos
        (add_nonneg (by norm_num only) (div_nonneg (by norm_num only) gammaFixedRadius_pos.le))
        (sub_nonpos.mpr hS)
  have hr : gammaFixedRadius ≤ gammaReflectedRoot L := by
    by_contra h
    have hm := gammaReflectedGap_strictMono hL (gammaReflectedRoot_pos hL) (lt_of_not_ge h)
    rw [gammaReflectedGap_root_eq_zero hL] at hm
    linarith only [hm, hg]
  have hs := (sq_le_sq₀ gammaFixedRadius_pos.le (gammaReflectedRoot_pos hL).le).mpr hr
  have hR : gammaFixedRadius ^ 2 = (40 / 99 : ℝ) * 35000 := Real.sq_sqrt (by norm_num only)
  change (35000 : ℝ) ≤ (99 / 40 : ℝ) * gammaReflectedRoot L ^ 2
  linarith only [hs, hR]

/-- At the exact reflected switch S2, G2 equals 35000. Combine both
one-sided inequalities by antisymmetry; the endpoint is included exactly. -/
theorem gammaReflected_at_switch : gammaReflectedBound gammaReflectedFixedSwitch = 35000 := by
  have hL : (100 : ℝ) ≤ gammaReflectedFixedSwitch := by
    linarith only [gammaReflectedFixedSwitch_bounds.1]
  exact le_antisymm (gammaReflected_le_fixed hL le_rfl) (fixed_le_gammaReflected hL le_rfl)

/-- For 100<=L<S2, G2(L)<35000. The fixed-radius gap is strictly positive,
so the reflected root is strictly smaller than the fixed radius. -/
theorem gammaReflected_lt_fixed {L : ℝ} (hL : 100 ≤ L) (hS : L < gammaReflectedFixedSwitch) :
    gammaReflectedBound L < 35000 := by
  have hg : 0 < gammaReflectedGap L gammaFixedRadius := by
    rw [gammaReflectedFixed_gap]
    exact
      mul_pos (add_pos (by norm_num only) (div_pos (by norm_num only) gammaFixedRadius_pos))
        (sub_pos.mpr hS)
  have hrle := gammaReflectedRoot_le_of_gap_nonneg hL gammaFixedRadius_pos hg.le
  have hrlt : gammaReflectedRoot L < gammaFixedRadius := by
    by_contra h
    have he := le_antisymm hrle (le_of_not_gt h)
    rw [← he, gammaReflectedGap_root_eq_zero hL] at hg
    exact lt_irrefl 0 hg
  have hs := (sq_lt_sq₀ (gammaReflectedRoot_pos hL).le gammaFixedRadius_pos.le).mpr hrlt
  have hR : gammaFixedRadius ^ 2 = (40 / 99 : ℝ) * 35000 := Real.sq_sqrt (by norm_num only)
  change (99 / 40 : ℝ) * gammaReflectedRoot L ^ 2 < 35000
  linarith only [hs, hR]

/-- The exact switch satisfies 209.8268<S2<209.8270. Tight rational
square-root brackets and exact gap signs certify both inequalities.
These decimals are only enclosures, not the definition of the switch. -/
theorem gammaReflectedSwitch_tight :
    (524567 / 2500 : ℝ) < gammaReflectedFixedSwitch ∧
      gammaReflectedFixedSwitch < 209827 / 1000 := by
  have hR : gammaFixedRadius ^ 2 = (40 / 99 : ℝ) * 35000 := Real.sq_sqrt (by norm_num only)
  have hrl : (59458839 / 500000 : ℝ) < gammaFixedRadius := by
    nlinarith only [hR, gammaFixedRadius_pos]
  have hru : gammaFixedRadius < (118917679 / 1000000 : ℝ) := by
    nlinarith only [hR, gammaFixedRadius_pos]
  have hD : 0 < (11783423 / 25000000 : ℝ) + (7 / 6) / gammaFixedRadius :=
    add_pos (by norm_num only) (div_pos (by norm_num only) gammaFixedRadius_pos)
  have hlo :=
    gammaReflectedGap_strictMono (by norm_num only : (100 : ℝ) ≤ 524567 / 2500) (by norm_num only)
      hrl
  have hhi :=
    gammaReflectedGap_strictMono (by norm_num only : (100 : ℝ) ≤ 209827 / 1000) gammaFixedRadius_pos
      hru
  have h0 : 0 < gammaReflectedGap (524567 / 2500) (59458839 / 500000) := by
    norm_num only [gammaReflectedGap]
  have h1 : gammaReflectedGap (209827 / 1000) (118917679 / 1000000) < 0 := by
    norm_num only [gammaReflectedGap]
  rw [gammaReflectedFixed_gap] at hlo hhi
  constructor
  · nlinarith only [hlo, h0, hD]
  · nlinarith only [hhi, h1, hD]

/-- For 109<=L<=112, the clipped third radius is at most L-34/5.
A correction cap at 112 places the first and second radii above 101;
monotonicity transfers the lower correction bound at that anchor. -/
theorem reflected_third_upper {L : ℝ} (hL : 109 ≤ L) (hU : L ≤ 112) :
    LLS.PaperStatements.endpointThirdRadius L ≤ L - 34 / 5 := by
  have hcap : LLS.PaperStatements.fullEndpointEvenGapCorrection 112 ≤ (71 / 10 : ℝ) := by
    have hc : LLS.PaperStatements.endpointCorrectionCheck 112 0 (71 / 10) = true := by
      decide +kernel
    simpa only [Rat.cast_ofNat, Rat.cast_div] using
      (LLS.PaperStatements.endpointCorrectionCheck_sound hc).2
  have h112 : LLS.PaperStatements.fullEndpointEvenGapCorrection L ≤ (71 / 10 : ℝ) :=
    (LLS.PaperStatements.fullEndpointEvenGapCorrection_strictMonoOn.monotoneOn
          (by linarith only [hL] : (8 : ℝ) ≤ L) (by norm_num only [Set.mem_Ici]) hU).trans
      hcap
  have ha : (101 : ℝ) ≤ LLS.PaperStatements.fullEndpointEvenCorrectionFirstRadius L :=
    (by linarith only [h112, hL] :
          (101 : ℝ) ≤ L - LLS.PaperStatements.fullEndpointEvenGapCorrection L).trans
      (le_max_right _ _)
  have hb :=
    ha.trans
      (LLS.PaperStatements.correction_second_gt (by linarith only [hL] : (45 / 4 : ℝ) ≤ L)).le
  have hcheck : LLS.PaperStatements.endpointCorrectionCheck 101 (34 / 5) 100 = true := by
    decide +kernel
  have h101 : (34 / 5 : ℝ) ≤ LLS.PaperStatements.fullEndpointEvenGapCorrection 101 := by
    simpa only [Rat.cast_ofNat, Rat.cast_div] using
      (LLS.PaperStatements.endpointCorrectionCheck_sound hcheck).1
  have hH :=
    h101.trans
      (LLS.PaperStatements.fullEndpointEvenGapCorrection_strictMonoOn.monotoneOn
        (by norm_num only : (8 : ℝ) ≤ 101)
        (by linarith only [hb] :
          (8 : ℝ) ≤ LLS.PaperStatements.fullEndpointEvenCorrectionSecondRadius L)
        hb)
  exact max_le (by linarith only [hL]) (by linarith only [hH])

/-- For 109<=L<=112 and q>=L-34/5 with q>=8, a correction cap
H(q)<=U implies fourth>=L-U. Compare the correction at the clipped
third radius using the preceding continuous bound. -/
theorem reflected_fourth_lower {L q U : ℝ} (hL : 109 ≤ L) (hU : L ≤ 112) (hq : 8 ≤ q)
    (hcq : L - 34 / 5 ≤ q) (hcap : LLS.PaperStatements.fullEndpointEvenGapCorrection q ≤ U) :
    L - U ≤ LLS.PaperStatements.endpointFourthRadius L := by
  have hc : (8 : ℝ) ≤ LLS.PaperStatements.endpointThirdRadius L := le_max_left _ _
  have hH :=
    (LLS.PaperStatements.fullEndpointEvenGapCorrection_strictMonoOn.monotoneOn hc hq
          ((reflected_third_upper hL hU).trans hcq)).trans
      hcap
  dsimp only [LLS.PaperStatements.endpointFourthRadius]
  linarith only [hH]

/-- For 109<=L<=110, G2<C4. A correction cap at 516/5 bounds the
fourth radius below, and a positive affine gap certifies the root comparison. -/
theorem gammaReflected_fourStep_band0 {L : ℝ} (hlo : (109 : ℝ) ≤ L) (hhi : L ≤ (110 : ℝ)) :
    gammaReflectedBound L < LLS.PaperStatements.endpointFourStepCutoff L := by
  have hc : LLS.PaperStatements.endpointCorrectionCheck (516 / 5) 0 (173 / 25) = true := by
    decide +kernel
  have hcap : LLS.PaperStatements.fullEndpointEvenGapCorrection (516 / 5 : ℝ) ≤ (173 / 25 : ℝ) := by
    simpa only [Rat.cast_ofNat, Rat.cast_div] using
      (LLS.PaperStatements.endpointCorrectionCheck_sound hc).2
  have hd :=
    reflected_fourth_lower (by linarith only [hlo] : (109 : ℝ) ≤ L) (by linarith only [hhi])
      (by norm_num only : (8 : ℝ) ≤ 516 / 5) (by linarith only [hhi]) hcap
  have hs :=
    gammaReflected_lt_affine_sq (L₀ := 109) (U := 173 / 25) (by linarith only [hlo]) hlo
      (by norm_num only) (by norm_num only) (by norm_num only [gammaReflectedGap])
  have hp : (0 : ℝ) ≤ L - (173 / 25) := by linarith only [hlo]
  exact hs.trans_le ((sq_le_sq₀ hp (hp.trans hd)).mpr hd)

/-- For 110<=L<=112, G2<C4. A correction cap at 526/5 and a positive
affine-gap anchor cover this entire closed real interval. -/
theorem gammaReflected_fourStep_band1 {L : ℝ} (hlo : (110 : ℝ) ≤ L) (hhi : L ≤ (112 : ℝ)) :
    gammaReflectedBound L < LLS.PaperStatements.endpointFourStepCutoff L := by
  have hc : LLS.PaperStatements.endpointCorrectionCheck (526 / 5) 0 (7) = true := by decide +kernel
  have hcap : LLS.PaperStatements.fullEndpointEvenGapCorrection (526 / 5 : ℝ) ≤ (7 : ℝ) := by
    simpa only [Rat.cast_ofNat, Rat.cast_div] using
      (LLS.PaperStatements.endpointCorrectionCheck_sound hc).2
  have hd :=
    reflected_fourth_lower (by linarith only [hlo] : (109 : ℝ) ≤ L) (by linarith only [hhi])
      (by norm_num only : (8 : ℝ) ≤ 526 / 5) (by linarith only [hhi]) hcap
  have hs :=
    gammaReflected_lt_affine_sq (L₀ := 110) (U := 7) (by linarith only [hlo]) hlo (by norm_num only)
      (by norm_num only) (by norm_num only [gammaReflectedGap])
  have hp : (0 : ℝ) ≤ L - (7) := by linarith only [hlo]
  exact hs.trans_le ((sq_le_sq₀ hp (hp.trans hd)).mpr hd)

/-- For 109<=L<=240, G2<C4. Combine the two new entrance intervals
with G2<G1 and the existing comparison above 112. -/
theorem gammaReflected_lt_fourStep {L : ℝ} (hL : 109 ≤ L) (hU : L ≤ 240) :
    gammaReflectedBound L < LLS.PaperStatements.endpointFourStepCutoff L := by
  by_cases h112 : L ≤ 112
  · by_cases h110 : L ≤ 110
    · exact gammaReflected_fourStep_band0 hL h110
    · exact gammaReflected_fourStep_band1 (le_of_not_ge h110) h112
  · exact
      (gammaReflected_lt_sharp (by linarith only [hL])).trans_le
        (sharp_le_fourStep_full (le_of_not_ge h112) hU)

/-- For every n>1 with 109<=log n<S2, G2 is strictly below the
existing public envelope. Compare its unresolved C4/G1 minimum, G1
and fixed-35000 branches on their exact selected intervals. -/
theorem gammaReflected_lt_improved {n : ℕ} (hn : 1 < n) (hL : 109 ≤ Real.log n)
    (hS : Real.log n < gammaReflectedFixedSwitch) :
    gammaReflectedBound (Real.log n) < improvedSelectedEnvelope n := by
  have h240 : Real.log n ≤ 240 := by linarith only [hS, gammaReflectedFixedSwitch_bounds.2]
  rw [← improved_eq_selected hn]
  by_cases h112 : Real.log n < 112
  · rw [improved_eq_middle_min hn (by linarith only [hL]) h112]
    exact
      lt_min (gammaReflected_lt_fourStep hL h240) (gammaReflected_lt_sharp (by linarith only [hL]))
  · by_cases hS1 : Real.log n ≤ gammaSharpFixedSwitch
    · rw [improved_eq_sharp hn (le_of_not_gt h112) hS1]
      exact gammaReflected_lt_sharp (by linarith only [hL])
    · rw [improved_eq_fixed35000 hn (le_of_not_ge hS1) h240]
      exact gammaReflected_lt_fixed (by linarith only [hL]) hS

end PseudoPrime.PrimeTestBounds.MillerRabin
