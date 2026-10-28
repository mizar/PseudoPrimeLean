/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.EndpointFixed67
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.PointwiseReciprocalLowerBound

/-! # Endpoint gaps retaining the pointwise reciprocal loss -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- The even endpoint gap with the Riemann reciprocal loss retained pointwise in y.
The additional term has positive sign and is independent of the conductor and pi-log
parameters. The character-side even reciprocal error remains unchanged. -/
noncomputable def endpointPointwiseGap (L P y z : ℝ) : ℝ :=
  fullEndpointEvenExactComparisonGap L P y z +
    2 * y ^ 2 * (y + 1 + z) * ((31551 / 20000 : ℝ) - Analysis.pointwiseReciprocalLoss y)

/-- For y>=8 and z>=0, the pointwise gap is at least the uniform-loss gap.
The established pointwise loss upper bound makes the added correction nonnegative. -/
theorem endpointPointwiseGap_ge {L P y z : ℝ} (hy : 8 ≤ y) (hz : 0 ≤ z) :
    fullEndpointEvenExactComparisonGap L P y z ≤ endpointPointwiseGap L P y z := by
  have hp :
    0 ≤ 2 * y ^ 2 * (y + 1 + z) * ((31551 / 20000 : ℝ) - Analysis.pointwiseReciprocalLoss y) := by
    exact
      mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num only) (sq_nonneg y)) (by linarith only [hy, hz]))
        (sub_nonneg.mpr (Analysis.pointwiseReciprocalLoss_le_uniform y))
  dsimp only [endpointPointwiseGap]
  linarith only [hp]

/-- For radius y>=2, the exact even pointwise comparison applies.
Retain the existing gap and use the generalized reciprocal and logarithmic bounds.
This supplies the low-radius prime witness certificates. -/
theorem pointwiseGap_nonpos {L P y z B S : ℝ} (hy : 2 ≤ y) (hz : 0 ≤ z)
    (hrec :
      2 * z - Analysis.pointwiseReciprocalLoss y ≤
        (1 / 2 : ℝ) * (1 - 1 / y ^ 2) * (L - P) - 1961 / 2000 + (2 * z + 103 / 80) / y ^ 2 -
          (1 - 1 / y) ^ 2 * B)
    (hupper : S ≤ (2 * y + 2 + 2 * z) * B + (L - P) * z + 103 / 250 - (23 / 40) * z - 2 * z ^ 2)
    (hlower : y ^ 2 - y / 20 - (1839 / 500 : ℝ) * z - 21 / 20 ≤ S) :
    endpointPointwiseGap L P y z ≤ 0 := by
  have hk : 0 ≤ (1 - 1 / y) ^ 2 := sq_nonneg (1 - 1 / y)
  have hC : 0 ≤ 2 * y + 2 + 2 * z := by nlinarith only [hy, hz]
  have hB :
    (1 - 1 / y) ^ 2 * B ≤
      (1 / 2 : ℝ) * (1 - 1 / y ^ 2) * (L - P) - 1961 / 2000 + (2 * z + 103 / 80) / y ^ 2 -
        (2 * z - Analysis.pointwiseReciprocalLoss y) := by
    linarith only [hrec]
  have hV :
    y ^ 2 - y / 20 - (1839 / 500 : ℝ) * z - 21 / 20 -
        ((L - P) * z + 103 / 250 - (23 / 40) * z - 2 * z ^ 2) ≤
      (2 * y + 2 + 2 * z) * B := by
    linarith only [hlower, hupper]
  have hVk := mul_le_mul_of_nonneg_left hV hk
  have hBk := mul_le_mul_of_nonneg_right hB hC
  have hscalar :
    (1 - 1 / y) ^ 2 *
        (y ^ 2 - y / 20 - (1839 / 500 : ℝ) * z - 21 / 20 -
          ((L - P) * z + 103 / 250 - (23 / 40) * z - 2 * z ^ 2)) ≤
      (2 * y + 2 + 2 * z) *
        ((1 / 2 : ℝ) * (1 - 1 / y ^ 2) * (L - P) - 1961 / 2000 + (2 * z + 103 / 80) / y ^ 2 -
          (2 * z - Analysis.pointwiseReciprocalLoss y)) := by
    nlinarith only [hVk, hBk]
  have hid :
    endpointPointwiseGap L P y z =
      y ^ 2 *
        ((1 - 1 / y) ^ 2 *
            (y ^ 2 - y / 20 - (1839 / 500 : ℝ) * z - 21 / 20 -
              ((L - P) * z + 103 / 250 - (23 / 40) * z - 2 * z ^ 2)) -
          (2 * y + 2 + 2 * z) *
            ((1 / 2 : ℝ) * (1 - 1 / y ^ 2) * (L - P) - 1961 / 2000 + (2 * z + 103 / 80) / y ^ 2 -
              (2 * z - Analysis.pointwiseReciprocalLoss y))) := by
    dsimp only [endpointPointwiseGap, fullEndpointEvenExactComparisonGap]
    ring
  rw [hid]
  exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg y) (by linarith only [hscalar])

/-- The pointwise scalar gap is nonpositive when the reciprocal and logarithmic
character upper bounds meet the Riemann logarithmic lower bound.
Multiply the signed comparisons by nonnegative factors, retaining the pointwise loss. -/
theorem endpointPointwiseGap_nonpos {L P y z B S : ℝ} (hy : 8 ≤ y) (hz : 0 ≤ z)
    (hrec :
      2 * z - Analysis.pointwiseReciprocalLoss y ≤
        (1 / 2 : ℝ) * (1 - 1 / y ^ 2) * (L - P) - 1961 / 2000 + (2 * z + 103 / 80) / y ^ 2 -
          (1 - 1 / y) ^ 2 * B)
    (hupper : S ≤ (2 * y + 2 + 2 * z) * B + (L - P) * z + 103 / 250 - (23 / 40) * z - 2 * z ^ 2)
    (hlower : y ^ 2 - y / 20 - (1839 / 500 : ℝ) * z - 21 / 20 ≤ S) :
    endpointPointwiseGap L P y z ≤ 0 := by
  exact pointwiseGap_nonpos (by linarith only [hy]) hz hrec hupper hlower

/-- For y>=1 and z>=0, increasing the pi-log parameter increases the pointwise gap.
The added reciprocal correction is independent of this parameter. -/
theorem endpointPointwiseGap_mono_pi {L P Q y z : ℝ} (hy : 1 ≤ y) (hz : 0 ≤ z) (hPQ : P ≤ Q) :
    endpointPointwiseGap L P y z ≤ endpointPointwiseGap L Q y z := by
  exact add_le_add (fullEndpointEvenExactComparisonGap_mono_pi hy hz hPQ) le_rfl

/-- For y>=1 and z>=0, increasing the conductor-log parameter decreases the pointwise gap.
The added reciprocal correction is independent of the conductor parameter. -/
theorem endpointPointwiseGap_antitone {L K P y z : ℝ} (hy : 1 ≤ y) (hz : 0 ≤ z) (hLK : L ≤ K) :
    endpointPointwiseGap K P y z ≤ endpointPointwiseGap L P y z := by
  exact add_le_add (fullEndpointEvenExactComparisonGap_antitone_level hy hz hLK) le_rfl

/-- For radius y>=2, the exact even pointwise comparison applies.
Retain the existing gap and use the generalized reciprocal and logarithmic bounds.
This supplies the low-radius prime witness certificates. -/
theorem primitive_pointwise_ne_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hq : 2 ≤ q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (heven : χ.Even) {y : ℝ} (hy : 2 ≤ y)
    (hgapPositive : 0 < endpointPointwiseGap (Real.log q) (2096 / 1831) y (Real.log y)) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ y ^ 2 ∧ χ p ≠ 1 := by
  by_contra hn
  have hypos : 0 < y := by linarith only [hy]
  have hz : 0 ≤ Real.log y := Real.log_nonneg (by linarith only [hy] : (1 : ℝ) ≤ y)
  have hy2 : 2 ≤ y ^ 2 := by nlinarith only [hy]
  have hx : 1 < y ^ 2 := by nlinarith only [hy]
  have ht : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ y ^ 2 → χ p = 1 := by
    intro p hprime hpy
    by_contra hv
    exact hn ⟨p, hprime, hpy, hv⟩
  have hRecId := reciprocalSum_re_eq_of_full_prime_trivial χ (sq_nonneg y) ht
  have hRecLower :=
    AnalyticNumberTheory.RiemannZeta.reciprocalWeightedMangoldtSum_ge_pointwise_loss hGRH.riemann
      hypos (by linarith only [hy2])
  rw [← hRecId] at hRecLower
  rw [Real.log_pow] at hRecLower
  norm_num only [Nat.cast_ofNat] at hRecLower
  have hError := Analysis.evenReciprocalError_le_exact (by linarith only [hy])
  have hRaw :=
    PseudoPrime.LLS.primitiveReciprocalRaw_even_le_of_mainError hq hGRH hp hne hinv heven
      (by linarith only [hx]) hError
  rw [Real.sqrt_sq (by linarith only [hy] : 0 ≤ y)] at hRaw
  have hrec :
    2 * Real.log y - Analysis.pointwiseReciprocalLoss y ≤
      (1 / 2 : ℝ) * (1 - 1 / y ^ 2) * (Real.log q - Real.log Real.pi) - 1961 / 2000 +
          (2 * Real.log y + 103 / 80) / y ^ 2 -
        (1 - 1 / y) ^ 2 * |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| := by
    nlinarith only [hRecLower, hRaw]
  have hpi0 : Real.pi < (31416 / 10000 : ℝ) := by
    calc
      Real.pi < 3.1416 := Real.pi_lt_d4
      _ = (31416 / 10000 : ℝ) := by norm_num only
  have hpi2 : Real.pi ^ 2 / 24 ≤ (103 / 250 : ℝ) := by
    have hsq : Real.pi ^ 2 ≤ (31416 / 10000 : ℝ) ^ 2 := by nlinarith only [Real.pi_pos, hpi0]
    nlinarith only [hsq]
  have hgamma : (23 / 40 : ℝ) ≤ Real.eulerMascheroniConstant :=
    Analysis.twentyThree_fortieths_lt_eulerMascheroniConstant.le
  have hMain :
    Analysis.primitiveLogEvenMainError (y ^ 2) ≤
      103 / 250 - (23 / 40) * Real.log y - 2 * (Real.log y) ^ 2 := by
    unfold Analysis.primitiveLogEvenMainError
    rw [Real.log_pow]
    nlinarith only [hpi2, hgamma, hz]
  have hLog :=
    AnalyticNumberTheory.DirichletLFunction.logSum_even_exact (x := y ^ 2) hq hGRH hp hne hinv heven
      hx
  rw [Real.sqrt_sq (by linarith only [hy] : 0 ≤ y), Real.log_pow] at hLog
  have hLogId := logWeightedSum_re_eq_of_full_prime_trivial χ (sq_nonneg y) ht
  rw [hLogId] at hLog
  have hupper :
    AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (y ^ 2) ≤
      (2 * y + 2 + 2 * Real.log y) * |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| +
          (Real.log q - Real.log Real.pi) * Real.log y +
          103 / 250 -
        (23 / 40) * Real.log y -
        2 * (Real.log y) ^ 2 := by
    nlinarith only [hLog, hMain]
  have hlower := PseudoPrime.LLS.logWeightedMangoldtSum_ge_rational_refined hGRH.riemann hx
  rw [Real.sqrt_sq (by linarith only [hy] : 0 ≤ y), Real.log_pow] at hlower
  have hlower' :
    y ^ 2 - y / 20 - (1839 / 500 : ℝ) * Real.log y - 21 / 20 ≤
      AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (y ^ 2) := by
    nlinarith only [hlower]
  have hgap :=
    pointwiseGap_nonpos hy hz hrec hupper hlower' (L := Real.log q) (P := Real.log Real.pi) (y := y)
      (z := Real.log y) (B := |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ|) (S :=
      AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (y ^ 2))
  have hgapPi :=
    endpointPointwiseGap_mono_pi (L := Real.log q) (P := (2096 / 1831 : ℝ)) (Q := Real.log Real.pi)
      (y := y) (z := Real.log y) (by linarith only [hy]) hz Analysis.log_pi_ge_2096_div_1831
  linarith only [hgap, hgapPositive, hgapPi]

/-- Under GRH, a primitive even nonprincipal character with positive pointwise gap
has a non-one prime through y^2. Replace only the Riemann reciprocal lower bound
in the existing endpoint argument; keep the even character-side error and logarithmic bounds. -/
theorem exists_prime_not_one_pointwise {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hq : 2 ≤ q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (heven : χ.Even) {y : ℝ} (hy : 8 ≤ y)
    (hgapPositive : 0 < endpointPointwiseGap (Real.log q) (2096 / 1831) y (Real.log y)) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ y ^ 2 ∧ χ p ≠ 1 := by
  exact primitive_pointwise_ne_one χ hq hGRH hp hne hinv heven (by linarith only [hy]) hgapPositive

/-- For radius y>=2, the exact even pointwise comparison applies.
Retain the existing gap and use the generalized reciprocal and logarithmic bounds.
This supplies the low-radius prime witness certificates. -/
theorem pointwise_ne_one_prime {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    (heven : χ.Even) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ}
    (hy : 2 ≤ y) (hgap : 0 < endpointPointwiseGap (Real.log q) (2096 / 1831) y (Real.log y)) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ y ^ 2 ∧ χ p ≠ 1 := by
  let _ : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hψ : χ.primitiveCharacter ≠ 1 :=
    AnalyticNumberTheory.Arithmetic.primitiveCharacter_ne_one χ hne
  have hq : 2 ≤ χ.conductor :=
    (Nat.two_le_iff _).mpr
      ⟨χ.conductor_ne_zero, fun he ↦ hne (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr he)⟩
  have hcond : χ.conductor ≤ q := Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level
  have hlog : Real.log χ.conductor ≤ Real.log q :=
    Real.log_le_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero χ.conductor_ne_zero))
      (Nat.cast_le.mpr hcond)
  have hy1 : 1 ≤ y := by linarith only [hy]
  have hz : 0 ≤ Real.log y := Real.log_nonneg hy1
  have hgapCond : 0 < endpointPointwiseGap (Real.log χ.conductor) (2096 / 1831) y (Real.log y) := by
    have hmono :=
      endpointPointwiseGap_antitone (L := Real.log χ.conductor) (K := Real.log q) (P :=
        (2096 / 1831 : ℝ)) (y := y) (z := Real.log y) hy1 hz hlog
    exact lt_of_lt_of_le hgap hmono
  obtain ⟨p, hp, hpy, hv⟩ :=
    primitive_pointwise_ne_one χ.primitiveCharacter hq hGRH χ.primitiveCharacter_isPrimitive hψ
      (inv_ne_one.mpr hψ) (reciprocalGap_primitiveCharacter_even heven) hy hgapCond
  refine ⟨p, hp, hpy, ?_⟩
  intro hone
  exact hv (primitiveCharacter_apply_one_of_apply_one χ hone)

/-- Under GRH, any even nonprincipal character with positive pointwise gap
at the ambient level has a non-one prime through y^2. Transfer the gap to its
primitive conductor by antitonicity and lift the non-one prime back to the ambient character. -/
theorem exists_prime_ne_one_pointwise {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    (heven : χ.Even) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ}
    (hy : 8 ≤ y) (hgap : 0 < endpointPointwiseGap (Real.log q) (2096 / 1831) y (Real.log y)) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ y ^ 2 ∧ χ p ≠ 1 := by
  exact pointwise_ne_one_prime χ hne heven hGRH (by linarith only [hy]) hgap

/-- A positive rational pointwise gap anchor with nonnegative quadratic coefficients
remains positive at the actual logarithm and all smaller conductor levels.
Use square monotonicity followed by conductor antitonicity. -/
theorem pointwise_gap_from_quad {L L₀ y z₀ a b : ℝ} (hL : L ≤ L₀) (hy : 1 ≤ y) (hz0 : 0 ≤ z₀)
    (hz : z₀ ≤ Real.log y) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hpoly :
      ∀ z : ℝ,
        endpointPointwiseGap L₀ (2096 / 1831) y z - endpointPointwiseGap L₀ (2096 / 1831) y z₀ =
          a * (z ^ 2 - z₀ ^ 2) + b * (z - z₀))
    (hanchor : 0 < endpointPointwiseGap L₀ (2096 / 1831) y z₀) :
    0 < endpointPointwiseGap L (2096 / 1831) y (Real.log y) := by
  have hzpos := hz0.trans hz
  have hsq := (sq_le_sq₀ hz0 hzpos).mpr hz
  have h1 := mul_nonneg ha (sub_nonneg.mpr hsq)
  have h2 := mul_nonneg hb (sub_nonneg.mpr hz)
  have hident := hpoly (Real.log y)
  have hgap : 0 < endpointPointwiseGap L₀ (2096 / 1831) y (Real.log y) := by
    linarith only [hanchor, hident, h1, h2]
  exact hgap.trans_le (endpointPointwiseGap_antitone hy hzpos hL)

/-- For L<=2877/250, the pointwise gap at radius 1637/200 is positive.
Reuse the existing logarithm anchor, verify the new rational quadratic gap,
and transport positivity to all smaller levels. This supports the fixed witness bound 61. -/
theorem endpointPointwise61_gap {L : ℝ} (hL : L ≤ 2877 / 250) :
    0 < endpointPointwiseGap L (2096 / 1831) (1637 / 200) (Real.log (1637 / 200 : ℝ)) := by
  apply
    pointwise_gap_from_quad (z₀ := 1051 / 500) (a := 7344507 / 20000) (b :=
      15915485245287839 / 16479000000000) hL (by norm_num only) (by norm_num only)
      endpoint61Sharp_log_lower (by norm_num only) (by norm_num only)
  · intro z
    dsimp only [endpointPointwiseGap, fullEndpointEvenExactComparisonGap,
      Analysis.pointwiseReciprocalLoss]
    ring
  · norm_num only [endpointPointwiseGap, fullEndpointEvenExactComparisonGap,
      Analysis.pointwiseReciprocalLoss]

end PseudoPrime.LLS.PaperStatements
