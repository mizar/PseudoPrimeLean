/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.FullEndpointEvenPolynomial
public import PseudoPrime.Analysis.LogTaylorBounds

/-! # Rational certificates for continuous endpoint-correction comparisons -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Polynomial numerator of the endpoint correction, with the logarithm supplied separately.
The field parameters permit exact rational evaluation and real specialization. -/
def endpointCorrectionNum {K : Type*} [Field K] (y z : K) : K :=
  36620000 * (3 * y + 1) * (y - 1) * z ^ 2 +
          (36620000 * y ^ 3 + 73100099 * y ^ 2 - 1528140 * y - 177204180) * z -
        56749471 * y ^ 3 +
      10777809 * y ^ 2 +
      2824690 * y -
    94877470

/-- Polynomial denominator of the endpoint correction. It is positive for y>=8 and z>=0. -/
def endpointCorrectionDen {K : Type*} [Field K] (y z : K) : K :=
  18310000 * (y - 1) * ((y + 1) ^ 2 + 2 * y * z)

/-- The correction is the quotient of the two polynomial evaluators at z=log y.
Expand the defining rational expression; this identity supports rational log enclosures. -/
theorem endpointCorrection_eq (y : ℝ) :
    fullEndpointEvenGapCorrection y =
      endpointCorrectionNum y (Real.log y) / endpointCorrectionDen y (Real.log y) := by
  unfold fullEndpointEvenGapCorrection fullEndpointEvenGapCorrectionNumerator
    fullEndpointEvenGapDenominator endpointCorrectionNum endpointCorrectionDen
  congr 1 <;> ring

/-- For y>=8, the numerator is monotone in a nonnegative logarithm argument.
Positive polynomial coefficients reduce the proof to square and linear monotonicity. -/
theorem endpointCorrectionNum_mono {y l u : ℝ} (hy : 8 ≤ y) (hl : 0 ≤ l) (hlu : l ≤ u) :
    endpointCorrectionNum y l ≤ endpointCorrectionNum y u := by
  have hy0 : 0 ≤ y := by linarith only [hy]
  have h2 := mul_nonneg hy0 (sub_nonneg.mpr hy)
  have h3 := mul_nonneg (sq_nonneg y) (sub_nonneg.mpr hy)
  have hA : 0 ≤ 36620000 * (3 * y + 1) * (y - 1) :=
    mul_nonneg (mul_nonneg (by norm_num only) (by linarith only [hy])) (by linarith only [hy])
  have hB : 0 ≤ 36620000 * y ^ 3 + 73100099 * y ^ 2 - 1528140 * y - 177204180 := by
    nlinarith only [hy, h2, h3]
  have hs := mul_le_mul_of_nonneg_left ((sq_le_sq₀ hl (hl.trans hlu)).mpr hlu) hA
  have hz := mul_le_mul_of_nonneg_left hlu hB
  dsimp only [endpointCorrectionNum]
  linarith only [hs, hz]

/-- For y>=8, the denominator is monotone in its logarithm argument.
Its linear coefficient is nonnegative. -/
theorem endpointCorrectionDen_mono {y l u : ℝ} (hy : 8 ≤ y) (hlu : l ≤ u) :
    endpointCorrectionDen y l ≤ endpointCorrectionDen y u := by
  have hp : 0 ≤ 36620000 * y * (y - 1) :=
    mul_nonneg (mul_nonneg (by norm_num only) (by linarith only [hy])) (by linarith only [hy])
  have hm := mul_le_mul_of_nonneg_left hlu hp
  dsimp only [endpointCorrectionDen]
  linarith only [hm]

/-- For y>=8 and z>=0, every denominator factor is positive.
This justifies clearing denominators in correction bounds. -/
theorem endpointCorrectionDen_pos {y z : ℝ} (hy : 8 ≤ y) (hz : 0 ≤ z) :
    0 < endpointCorrectionDen y z := by
  exact
    mul_pos (mul_pos (by norm_num only) (by linarith only [hy]))
      (add_pos_of_pos_of_nonneg (sq_pos_of_pos (by linarith only [hy] : 0 < y + 1))
        (mul_nonneg (mul_nonneg (by norm_num only) (by linarith only [hy])) hz))

/-- Given logarithm enclosures and cross-multiplied polynomial bounds, enclose the correction.
Monotonicity of both polynomials and denominator positivity prove both inequalities. -/
theorem endpointCorrection_bounds {y l u a b : ℝ} (hy : 8 ≤ y) (hl0 : 0 ≤ l) (hl : l ≤ Real.log y)
    (hu : Real.log y ≤ u) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hlo : a * endpointCorrectionDen y u ≤ endpointCorrectionNum y l)
    (hhi : endpointCorrectionNum y u ≤ b * endpointCorrectionDen y l) :
    a ≤ fullEndpointEvenGapCorrection y ∧ fullEndpointEvenGapCorrection y ≤ b := by
  have hnlo := endpointCorrectionNum_mono hy hl0 hl
  have hnhi := endpointCorrectionNum_mono hy (hl0.trans hl) hu
  have hdlo := endpointCorrectionDen_mono hy hl
  have hdhi := endpointCorrectionDen_mono hy hu
  have hdpos := endpointCorrectionDen_pos hy (hl0.trans hl)
  rw [endpointCorrection_eq]
  constructor
  · apply (le_div_iff₀ hdpos).mpr
    exact (mul_le_mul_of_nonneg_left hdhi ha).trans (hlo.trans hnlo)
  · apply (div_le_iff₀ hdpos).mpr
    exact hnhi.trans (hhi.trans (mul_le_mul_of_nonneg_left hdlo hb))

/-- Choose a power-of-two scale for positive rational anchors between eight and 256.
The checker independently verifies convergence, so other inputs cannot yield unsound claims. -/
def endpointLogScale (q : ℚ) : ℕ :=
  if q ≤ 12 then 3
  else if q ≤ 24 then 4 else if q ≤ 48 then 5 else if q ≤ 96 then 6 else if q ≤ 192 then 7 else 8

/-- Check a rational correction enclosure using sixteen terms of the logarithm series.
All domain and sign requirements are part of the Boolean certificate. -/
def endpointCorrectionCheck (q a b : ℚ) : Bool :=
  let j := endpointLogScale q
  let l := Analysis.rationalLogLower q j 16
  let u := Analysis.rationalLogUpper q j 16
  decide
    (8 ≤ q ∧
      |1 - q / 2 ^ j| < 1 ∧
      0 ≤ l ∧
      0 ≤ a ∧
      0 ≤ b ∧
      a * endpointCorrectionDen q u ≤ endpointCorrectionNum q l ∧
      endpointCorrectionNum q u ≤ b * endpointCorrectionDen q l)

/-- Rational numerator evaluation commutes with casting to the reals.
Expand the polynomial and distribute casts. -/
theorem endpointCorrectionNum_cast (y z : ℚ) :
    ((endpointCorrectionNum y z : ℚ) : ℝ) = endpointCorrectionNum (y : ℝ) (z : ℝ) := by
  norm_num only [endpointCorrectionNum, Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_pow,
    Rat.cast_ofNat]

/-- Rational denominator evaluation commutes with casting to the reals.
Expand the polynomial and distribute casts. -/
theorem endpointCorrectionDen_cast (y z : ℚ) :
    ((endpointCorrectionDen y z : ℚ) : ℝ) = endpointCorrectionDen (y : ℝ) (z : ℝ) := by
  norm_num only [endpointCorrectionDen, Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_pow,
    Rat.cast_ofNat, Rat.cast_one]

/-- A successful rational check encloses the real endpoint correction.
Apply the certified logarithm bounds and polynomial comparison theorem. -/
theorem endpointCorrectionCheck_sound {q a b : ℚ} (h : endpointCorrectionCheck q a b = true) :
    (a : ℝ) ≤ fullEndpointEvenGapCorrection (q : ℝ) ∧
      fullEndpointEvenGapCorrection (q : ℝ) ≤ (b : ℝ) := by
  rcases of_decide_eq_true h with ⟨hq, hx, hl0, ha, hb, hlo, hhi⟩
  have hlog :=
    Analysis.rationalLogBounds_sound (by linarith only [hq] : (0 : ℚ) < q) (endpointLogScale q) 16
      hx
  apply
    endpointCorrection_bounds (by exact_mod_cast hq) (by exact_mod_cast hl0) hlog.1 hlog.2
      (by exact_mod_cast ha) (by exact_mod_cast hb)
  · have h := (Rat.cast_le (K := ℝ)).mpr hlo
    simpa only [Rat.cast_mul, endpointCorrectionDen_cast, endpointCorrectionNum_cast] using h
  · have h := (Rat.cast_le (K := ℝ)).mpr hhi
    simpa only [Rat.cast_mul, endpointCorrectionDen_cast, endpointCorrectionNum_cast] using h

/-- One continuous comparison cell with rational endpoints, target slope and intercept,
and upper/lower correction bounds. The checker verifies all required inequalities.
Cells are chained to cover a complete interval without sampling real inputs. -/
structure EndpointOrderCell where
  left : ℚ
  right : ℚ
  slope : ℚ
  intercept : ℚ
  upper : ℚ
  lower : ℚ

/-- Check the two correction anchors and the affine inequality at the cell endpoint.
The slope condition extends the endpoint inequality to every real input in the cell. -/
def EndpointOrderCell.check (c : EndpointOrderCell) : Bool :=
  endpointCorrectionCheck c.right 0 c.upper &&
    endpointCorrectionCheck (c.left - c.upper) c.lower 100 &&
    decide
      (8 ≤ c.left - c.upper ∧ c.slope ≤ 1 ∧ c.right - c.lower < c.slope * c.right + c.intercept)

/-- For a checked cell and L in its interval with L>=23/2, the second radius
is below the target affine function. Correction monotonicity controls both stages. -/
theorem EndpointOrderCell.sound {c : EndpointOrderCell} (hc : c.check = true) {L : ℝ}
    (hL : 23 / 2 ≤ L) (hlo : (c.left : ℝ) ≤ L) (hhi : L ≤ (c.right : ℝ)) :
    fullEndpointEvenCorrectionSecondRadius L < (c.slope : ℝ) * L + (c.intercept : ℝ) := by
  have hsplit := Bool.and_eq_true_iff.mp hc
  have hpair := Bool.and_eq_true_iff.mp hsplit.1
  have hup := (endpointCorrectionCheck_sound hpair.1).2
  have hdown := (endpointCorrectionCheck_sound hpair.2).1
  rcases of_decide_eq_true hsplit.2 with ⟨ha8, hs, ht⟩
  have ha8R : (8 : ℝ) ≤ (c.left : ℝ) - (c.upper : ℝ) := by exact_mod_cast ha8
  have hmono := fullEndpointEvenGapCorrection_strictMonoOn.monotoneOn
  have hHU :=
    (hmono (by linarith only [hL] : (8 : ℝ) ≤ L) (by linarith only [hL, hhi] : (8 : ℝ) ≤ c.right)
          hhi).trans
      hup
  have hA : (c.left : ℝ) - (c.upper : ℝ) ≤ fullEndpointEvenCorrectionFirstRadius L := by
    exact
      (by linarith only [hHU, hlo] :
            (c.left : ℝ) - (c.upper : ℝ) ≤ L - fullEndpointEvenGapCorrection L).trans
        (le_max_right _ _)
  have hfirst : (8 : ℝ) ≤ fullEndpointEvenCorrectionFirstRadius L := le_max_left _ _
  have hHV :
    (c.lower : ℝ) ≤ fullEndpointEvenGapCorrection (fullEndpointEvenCorrectionFirstRadius L) := by
    have hreal : (c.lower : ℝ) ≤ fullEndpointEvenGapCorrection ((c.left : ℝ) - (c.upper : ℝ)) := by
      simpa only [Rat.cast_sub] using hdown
    exact hreal.trans (hmono ha8R hfirst hA)
  have hsR : (c.slope : ℝ) ≤ 1 := by exact_mod_cast hs
  have htR : (c.right : ℝ) - (c.lower : ℝ) < (c.slope : ℝ) * (c.right : ℝ) + (c.intercept : ℝ) := by
    exact_mod_cast ht
  have hmul := mul_nonneg (sub_nonneg.mpr hsR) (sub_nonneg.mpr hhi)
  dsimp only [fullEndpointEvenCorrectionSecondRadius]
  nlinarith only [hHV, htR, hmul]

/-- Check an overlapping list of comparison cells covering the requested interval.
Each cell must use the requested affine target, and coverage must reach the right endpoint. -/
def endpointBandCheck (a b slope intercept : ℚ) : List EndpointOrderCell → Bool
  | [] => false
  | c :: cs =>
    decide (c.left ≤ a ∧ c.slope = slope ∧ c.intercept = intercept) && c.check &&
      if b ≤ c.right then true else endpointBandCheck c.right b slope intercept cs

/-- A successful band check bounds the second radius throughout the real interval.
Induct on the covering list and apply the first cell containing the input. -/
theorem endpointBandCheck_sound {a b slope intercept : ℚ} {cs : List EndpointOrderCell}
    (hc : endpointBandCheck a b slope intercept cs = true) {L : ℝ} (hL : 23 / 2 ≤ L)
    (hlo : (a : ℝ) ≤ L) (hhi : L ≤ (b : ℝ)) :
    fullEndpointEvenCorrectionSecondRadius L < (slope : ℝ) * L + (intercept : ℝ) := by
  induction cs generalizing a with
  | nil => contradiction
  | cons c cs ih =>
    have hp := Bool.and_eq_true_iff.mp hc
    have hp0 := Bool.and_eq_true_iff.mp hp.1
    rcases of_decide_eq_true hp0.1 with ⟨hca, hs, ht⟩
    by_cases hright : L ≤ (c.right : ℝ)
    · have ha : (c.left : ℝ) ≤ L := ((Rat.cast_le (K := ℝ)).mpr hca).trans hlo
      have h := EndpointOrderCell.sound hp0.2 hL ha hright
      simpa only [hs, ht] using h
    · have hnb : ¬b ≤ c.right := by
        intro h
        exact hright (hhi.trans ((Rat.cast_le (K := ℝ)).mpr h))
      have hnext : endpointBandCheck c.right b slope intercept cs = true := by
        simpa only [ite_eq_right hnb] using hp.2
      exact ih hnext (le_of_not_ge hright)

/-- Rational covering cells for endpoint comparison band 0.
The checked correction bounds imply a continuous affine bound for the second radius. -/
def endpointOrderBand0 : List EndpointOrderCell :=
  [⟨(74 / 5), (4499 / 250), (8 / 9), (-14 / 9), (556 / 125), (913 / 250)⟩,
    ⟨(4499 / 250), 22, (8 / 9), (-14 / 9), (4723 / 1000), (2009 / 500)⟩]

/-- The exact rational certificates for band 0 pass kernel reduction.
These certify interval coverage and correction inequalities, rather than sampled inputs. -/
theorem endpointOrderBand0_check :
    endpointBandCheck (74 / 5) 22 (8 / 9) (-14 / 9) endpointOrderBand0 = true := by decide +kernel

/-- Throughout comparison band 0, the second radius is below the stated affine bound.
Apply the checked covering certificate; this is used to eliminate dominated endpoint branches. -/
theorem endpointOrderBand0_sound {L : ℝ} (hlo : ((74 / 5) : ℝ) ≤ L) (hhi : L ≤ (22 : ℝ)) :
    fullEndpointEvenCorrectionSecondRadius L < ((8 / 9) : ℝ) * L + ((-14 / 9) : ℝ) := by
  have h :=
    endpointBandCheck_sound (L := L) endpointOrderBand0_check (by linarith only [hlo])
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hlo)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hhi)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using h

/-- Rational covering cells for endpoint comparison band 1.
The checked correction bounds imply a continuous affine bound for the second radius. -/
def endpointOrderBand1 : List EndpointOrderCell :=
  [⟨22, (111 / 4), (9 / 10), (-63 / 40), (2519 / 500), (4363 / 1000)⟩]

/-- The exact rational certificates for band 1 pass kernel reduction.
These certify interval coverage and correction inequalities, rather than sampled inputs. -/
theorem endpointOrderBand1_check :
    endpointBandCheck 22 (111 / 4) (9 / 10) (-63 / 40) endpointOrderBand1 = true := by
  decide +kernel

/-- Throughout comparison band 1, the second radius is below the stated affine bound.
Apply the checked covering certificate; this is used to eliminate dominated endpoint branches. -/
theorem endpointOrderBand1_sound {L : ℝ} (hlo : (22 : ℝ) ≤ L) (hhi : L ≤ ((111 / 4) : ℝ)) :
    fullEndpointEvenCorrectionSecondRadius L < ((9 / 10) : ℝ) * L + ((-63 / 40) : ℝ) := by
  have h :=
    endpointBandCheck_sound (L := L) endpointOrderBand1_check (by linarith only [hlo])
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hlo)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hhi)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using h

/-- Rational covering cells for endpoint comparison band 2.
The checked correction bounds imply a continuous affine bound for the second radius. -/
def endpointOrderBand2 : List EndpointOrderCell :=
  [⟨(111 / 4), (14279 / 500), 0, 24, (5077 / 1000), (4761 / 1000)⟩,
    ⟨(14279 / 500), (144 / 5), 0, 24, (636 / 125), (601 / 125)⟩]

/-- The exact rational certificates for band 2 pass kernel reduction.
These certify interval coverage and correction inequalities, rather than sampled inputs. -/
theorem endpointOrderBand2_check :
    endpointBandCheck (111 / 4) (144 / 5) 0 24 endpointOrderBand2 = true := by decide +kernel

/-- Throughout comparison band 2, the second radius is below the stated affine bound.
Apply the checked covering certificate; this is used to eliminate dominated endpoint branches. -/
theorem endpointOrderBand2_sound {L : ℝ} (hlo : ((111 / 4) : ℝ) ≤ L) (hhi : L ≤ ((144 / 5) : ℝ)) :
    fullEndpointEvenCorrectionSecondRadius L < (0 : ℝ) * L + (24 : ℝ) := by
  have h :=
    endpointBandCheck_sound (L := L) endpointOrderBand2_check (by linarith only [hlo])
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hlo)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hhi)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using h

/-- Rational covering cells for endpoint comparison band 3.
The checked correction bounds imply a continuous affine bound for the second radius. -/
def endpointOrderBand3 : List EndpointOrderCell :=
  [⟨(144 / 5), (8399 / 250), (800 / 837), (-304 / 93), (2649 / 500), (4809 / 1000)⟩,
    ⟨(8399 / 250), (369 / 10), (800 / 837), (-304 / 93), (5427 / 1000), (1011 / 200)⟩]

/-- The exact rational certificates for band 3 pass kernel reduction.
These certify interval coverage and correction inequalities, rather than sampled inputs. -/
theorem endpointOrderBand3_check :
    endpointBandCheck (144 / 5) (369 / 10) (800 / 837) (-304 / 93) endpointOrderBand3 = true := by
  decide +kernel

/-- Throughout comparison band 3, the second radius is below the stated affine bound.
Apply the checked covering certificate; this is used to eliminate dominated endpoint branches. -/
theorem endpointOrderBand3_sound {L : ℝ} (hlo : ((144 / 5) : ℝ) ≤ L) (hhi : L ≤ ((369 / 10) : ℝ)) :
    fullEndpointEvenCorrectionSecondRadius L < ((800 / 837) : ℝ) * L + ((-304 / 93) : ℝ) := by
  have h :=
    endpointBandCheck_sound (L := L) endpointOrderBand3_check (by linarith only [hlo])
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hlo)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hhi)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using h

/-- Rational covering cells for endpoint comparison band 4.
The checked correction bounds imply a continuous affine bound for the second radius. -/
def endpointOrderBand4 : List EndpointOrderCell :=
  [⟨(369 / 10), (5331 / 125), (3200 / 3337), (-11296 / 3337), (5627 / 1000), (5197 / 1000)⟩,
    ⟨(5331 / 125), (48201 / 1000), (3200 / 3337), (-11296 / 3337), (2899 / 500), (2711 / 500)⟩,
    ⟨(48201 / 1000), (10717 / 200), (3200 / 3337), (-11296 / 3337), (1487 / 250), (5611 / 1000)⟩]

/-- The exact rational certificates for band 4 pass kernel reduction.
These certify interval coverage and correction inequalities, rather than sampled inputs. -/
theorem endpointOrderBand4_check :
    endpointBandCheck (369 / 10) (10717 / 200) (3200 / 3337) (-11296 / 3337) endpointOrderBand4 =
      true := by
  decide +kernel

/-- Throughout comparison band 4, the second radius is below the stated affine bound.
Apply the checked covering certificate; this is used to eliminate dominated endpoint branches. -/
theorem endpointOrderBand4_sound {L : ℝ} (hlo : ((369 / 10) : ℝ) ≤ L)
    (hhi : L ≤ ((10717 / 200) : ℝ)) :
    fullEndpointEvenCorrectionSecondRadius L < ((3200 / 3337) : ℝ) * L + ((-11296 / 3337) : ℝ) := by
  have h :=
    endpointBandCheck_sound (L := L) endpointOrderBand4_check (by linarith only [hlo])
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hlo)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hhi)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using h

/-- Rational covering cells for endpoint comparison band 5.
The checked correction bounds imply a continuous affine bound for the second radius. -/
def endpointOrderBand5 : List EndpointOrderCell :=
  [⟨(10717 / 200), (59677 / 1000), (3200 / 3281), (-13984 / 3281), (6103 / 1000), (2887 / 500)⟩,
    ⟨(59677 / 1000), (66307 / 1000), (3200 / 3281), (-13984 / 3281), (782 / 125), (5941 / 1000)⟩,
    ⟨(66307 / 1000), (6999 / 100), (3200 / 3281), (-13984 / 3281), (1267 / 200), (6107 / 1000)⟩]

/-- The exact rational certificates for band 5 pass kernel reduction.
These certify interval coverage and correction inequalities, rather than sampled inputs. -/
theorem endpointOrderBand5_check :
    endpointBandCheck (10717 / 200) (6999 / 100) (3200 / 3281) (-13984 / 3281) endpointOrderBand5 =
      true := by
  decide +kernel

/-- Throughout comparison band 5, the second radius is below the stated affine bound.
Apply the checked covering certificate; this is used to eliminate dominated endpoint branches. -/
theorem endpointOrderBand5_sound {L : ℝ} (hlo : ((10717 / 200) : ℝ) ≤ L)
    (hhi : L ≤ ((6999 / 100) : ℝ)) :
    fullEndpointEvenCorrectionSecondRadius L < ((3200 / 3281) : ℝ) * L + ((-13984 / 3281) : ℝ) := by
  have h :=
    endpointBandCheck_sound (L := L) endpointOrderBand5_check (by linarith only [hlo])
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hlo)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hhi)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using h

/-- Rational covering cells for endpoint comparison band 6.
The checked correction bounds imply a continuous affine bound for the second radius. -/
def endpointOrderBand6 : List EndpointOrderCell :=
  [⟨(6999 / 100), (78739 / 1000), (3200 / 3259), (-15392 / 3259), (6509 / 1000), (6189 / 1000)⟩,
    ⟨(78739 / 1000), (22177 / 250), (3200 / 3259), (-15392 / 3259), (6689 / 1000), (3187 / 500)⟩,
    ⟨(22177 / 250), (49549 / 500), (3200 / 3259), (-15392 / 3259), (3429 / 500), (1641 / 250)⟩,
    ⟨(49549 / 500), (54521 / 500), (3200 / 3259), (-15392 / 3259), (3503 / 500), (3371 / 500)⟩,
    ⟨(54521 / 500), (2947 / 25), (3200 / 3259), (-15392 / 3259), (891 / 125), (3449 / 500)⟩,
    ⟨(2947 / 25), 122, (3200 / 3259), (-15392 / 3259), (3591 / 500), (3513 / 500)⟩]

/-- The exact rational certificates for band 6 pass kernel reduction.
These certify interval coverage and correction inequalities, rather than sampled inputs. -/
theorem endpointOrderBand6_check :
    endpointBandCheck (6999 / 100) 122 (3200 / 3259) (-15392 / 3259) endpointOrderBand6 = true := by
  decide +kernel

/-- Throughout comparison band 6, the second radius is below the stated affine bound.
Apply the checked covering certificate; this is used to eliminate dominated endpoint branches. -/
theorem endpointOrderBand6_sound {L : ℝ} (hlo : ((6999 / 100) : ℝ) ≤ L) (hhi : L ≤ (122 : ℝ)) :
    fullEndpointEvenCorrectionSecondRadius L < ((3200 / 3259) : ℝ) * L + ((-15392 / 3259) : ℝ) := by
  have h :=
    endpointBandCheck_sound (L := L) endpointOrderBand6_check (by linarith only [hlo])
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hlo)
      (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hhi)
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_zero] using h

end PseudoPrime.LLS.PaperStatements
