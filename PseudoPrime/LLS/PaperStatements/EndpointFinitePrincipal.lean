/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.EndpointPointwise
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.PointwiseReciprocalLowerBound

/-! # Principal endpoint comparison with certified finite gains -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- The pointwise comparison gap retaining both finite principal gains. -/
noncomputable def finitePrincipalGap (L P y z dR dS : ℝ) : ℝ :=
  endpointPointwiseGap L P y z + (y - 1) ^ 2 * dS + 2 * y ^ 2 * (y + 1 + z) * dR

/-- Multiplication by the squared radius cancels the reciprocal factor. -/
theorem finitePrincipal_radius_cancel {y : ℝ} (hy : 2 ≤ y) :
    y ^ 2 * (1 - 1 / y) ^ 2 = (y - 1) ^ 2 := by
  have hy0 : y ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 2) hy)
  have h : y * (1 - 1 / y) = y - 1 := by
    rw [mul_sub, mul_one, div_eq_mul_inv, one_mul, mul_inv_cancel₀ hy0]
  rw [← mul_pow, h]

/-- The gain admits the scalar form used by the principal comparison. -/
theorem finitePrincipalGap_eq {L P y z dR dS : ℝ} (hy : 2 ≤ y) :
    finitePrincipalGap L P y z dR dS =
      endpointPointwiseGap L P y z + y ^ 2 * (1 - 1 / y) ^ 2 * dS +
        2 * y ^ 2 * (y + 1 + z) * dR := by
  rw [finitePrincipalGap, finitePrincipal_radius_cancel hy]

/-- Increasing the pi-log parameter increases the gained gap. -/
theorem finitePrincipalGap_mono_pi {L P Q y z dR dS : ℝ} (hy : 1 ≤ y) (hz : 0 ≤ z) (hPQ : P ≤ Q) :
    finitePrincipalGap L P y z dR dS ≤ finitePrincipalGap L Q y z dR dS := by
  exact add_le_add (add_le_add (endpointPointwiseGap_mono_pi hy hz hPQ) le_rfl) le_rfl

/-- Increasing the conductor-log parameter decreases the gained gap. -/
theorem finitePrincipalGap_antitone {L K P y z dR dS : ℝ} (hy : 1 ≤ y) (hz : 0 ≤ z) (hLK : L ≤ K) :
    finitePrincipalGap K P y z dR dS ≤ finitePrincipalGap L P y z dR dS := by
  exact add_le_add (add_le_add (endpointPointwiseGap_antitone hy hz hLK) le_rfl) le_rfl

/-- The strengthened actual principal lower bounds force a nonpositive gap. -/
theorem finitePrincipalGap_nonpos {L P y z B S dR dS : ℝ} (hy : 2 ≤ y) (hz : 0 ≤ z)
    (hrec :
      2 * z - Analysis.pointwiseReciprocalLoss y + dR ≤
        (1 / 2 : ℝ) * (1 - 1 / y ^ 2) * (L - P) - 1961 / 2000 + (2 * z + 103 / 80) / y ^ 2 -
          (1 - 1 / y) ^ 2 * B)
    (hupper : S ≤ (2 * y + 2 + 2 * z) * B + (L - P) * z + 103 / 250 - (23 / 40) * z - 2 * z ^ 2)
    (hlower : y ^ 2 - y / 20 - (1839 / 500 : ℝ) * z - 21 / 20 + dS ≤ S) :
    finitePrincipalGap L P y z dR dS ≤ 0 := by
  have hk : 0 ≤ (1 - 1 / y) ^ 2 := sq_nonneg (1 - 1 / y)
  have hC : 0 ≤ 2 * y + 2 + 2 * z := by nlinarith only [hy, hz]
  have hB :
    (1 - 1 / y) ^ 2 * B ≤
      (1 / 2 : ℝ) * (1 - 1 / y ^ 2) * (L - P) - 1961 / 2000 + (2 * z + 103 / 80) / y ^ 2 -
        (2 * z - Analysis.pointwiseReciprocalLoss y + dR) := by
    linarith only [hrec]
  have hV :
    y ^ 2 - y / 20 - (1839 / 500 : ℝ) * z - 21 / 20 + dS -
        ((L - P) * z + 103 / 250 - (23 / 40) * z - 2 * z ^ 2) ≤
      (2 * y + 2 + 2 * z) * B := by
    linarith only [hlower, hupper]
  have hVk := mul_le_mul_of_nonneg_left hV hk
  have hBk := mul_le_mul_of_nonneg_right hB hC
  have hscalar :
    (1 - 1 / y) ^ 2 *
        (y ^ 2 - y / 20 - (1839 / 500 : ℝ) * z - 21 / 20 + dS -
          ((L - P) * z + 103 / 250 - (23 / 40) * z - 2 * z ^ 2)) ≤
      (2 * y + 2 + 2 * z) *
        ((1 / 2 : ℝ) * (1 - 1 / y ^ 2) * (L - P) - 1961 / 2000 + (2 * z + 103 / 80) / y ^ 2 -
          (2 * z - Analysis.pointwiseReciprocalLoss y + dR)) := by
    nlinarith only [hVk, hBk]
  have hid :
    finitePrincipalGap L P y z dR dS =
      y ^ 2 *
        ((1 - 1 / y) ^ 2 *
            (y ^ 2 - y / 20 - (1839 / 500 : ℝ) * z - 21 / 20 + dS -
              ((L - P) * z + 103 / 250 - (23 / 40) * z - 2 * z ^ 2)) -
          (2 * y + 2 + 2 * z) *
            ((1 / 2 : ℝ) * (1 - 1 / y ^ 2) * (L - P) - 1961 / 2000 + (2 * z + 103 / 80) / y ^ 2 -
              (2 * z - Analysis.pointwiseReciprocalLoss y + dR))) := by
    rw [finitePrincipalGap_eq hy]
    dsimp only [endpointPointwiseGap, fullEndpointEvenExactComparisonGap]
    ring
  rw [hid]
  exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg y) (by linarith only [hscalar])

/-- A primitive even character has a prime witness from actual finite principal bounds. -/
theorem primitive_finitePrincipal_ne_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hq : 2 ≤ q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (heven : χ.Even) {y : ℝ} (hy : 2 ≤ y) (dR dS : ℝ)
    (hR :
      2 * Real.log y - Analysis.pointwiseReciprocalLoss y + dR ≤
        AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtSum (y ^ 2))
    (hS :
      y ^ 2 - y / 20 - (1839 / 500 : ℝ) * Real.log y - 21 / 20 + dS ≤
        AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (y ^ 2))
    (hgapPositive : 0 < finitePrincipalGap (Real.log q) (2096 / 1831) y (Real.log y) dR dS) :
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
  have hRecLower := hR
  rw [← hRecId] at hRecLower
  have hError := Analysis.evenReciprocalError_le_exact (by linarith only [hy])
  have hRaw :=
    PseudoPrime.LLS.primitiveReciprocalRaw_even_le_of_mainError hq hGRH hp hne hinv heven
      (by linarith only [hx]) hError
  rw [Real.sqrt_sq (by linarith only [hy] : 0 ≤ y)] at hRaw
  have hrec :
    2 * Real.log y - Analysis.pointwiseReciprocalLoss y + dR ≤
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
  have hgap :=
    finitePrincipalGap_nonpos hy hz hrec hupper hS (L := Real.log q) (P := Real.log Real.pi) (y :=
      y) (z := Real.log y) (B := |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ|) (S :=
      AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (y ^ 2))
  have hgapPi :=
    finitePrincipalGap_mono_pi (L := Real.log q) (P := (2096 / 1831 : ℝ)) (Q := Real.log Real.pi)
      (y := y) (z := Real.log y) (dR := dR) (dS := dS) (by linarith only [hy]) hz
      Analysis.log_pi_ge_2096_div_1831
  linarith only [hgap, hgapPositive, hgapPi]

/-- Transfer the finite principal witness from the conductor to the ambient level. -/
theorem finitePrincipal_ne_one_prime {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    (heven : χ.Even) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ}
    (hy : 2 ≤ y) (dR dS : ℝ)
    (hR :
      2 * Real.log y - Analysis.pointwiseReciprocalLoss y + dR ≤
        AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtSum (y ^ 2))
    (hS :
      y ^ 2 - y / 20 - (1839 / 500 : ℝ) * Real.log y - 21 / 20 + dS ≤
        AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (y ^ 2))
    (hgap : 0 < finitePrincipalGap (Real.log q) (2096 / 1831) y (Real.log y) dR dS) :
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
  have hgapCond :
    0 < finitePrincipalGap (Real.log χ.conductor) (2096 / 1831) y (Real.log y) dR dS := by
    have hmono :=
      finitePrincipalGap_antitone (L := Real.log χ.conductor) (K := Real.log q) (P :=
        (2096 / 1831 : ℝ)) (y := y) (z := Real.log y) (dR := dR) (dS := dS) hy1 hz hlog
    exact lt_of_lt_of_le hgap hmono
  obtain ⟨p, hp, hpy, hv⟩ :=
    primitive_finitePrincipal_ne_one χ.primitiveCharacter hq hGRH χ.primitiveCharacter_isPrimitive
      hψ (inv_ne_one.mpr hψ) (reciprocalGap_primitiveCharacter_even heven) hy dR dS hR hS hgapCond
  refine ⟨p, hp, hpy, ?_⟩
  intro hone
  exact hv (primitiveCharacter_apply_one_of_apply_one χ hone)

end PseudoPrime.LLS.PaperStatements
