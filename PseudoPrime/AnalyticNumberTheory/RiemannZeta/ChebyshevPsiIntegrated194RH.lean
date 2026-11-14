/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevIntegratedCompare194
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiIntegratedImprovedRH
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroReciprocalIntegratedBracketsRH

/-! # Integrated ψ envelope above log height 97/5 -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- At the canonical scale, the logarithmic zero-cutoff argument simplifies to exp(L/2)/(5L/6). -/
theorem integrated_cutoff_log_arg {L : ℝ} (hL : (97 / 5 : ℝ) ≤ L) :
    let s := Real.exp (L / 2)
    let q := 5 * L / (6 * Real.pi)
    let δ := q / s
    (2 / δ) / (2 * Real.pi) = s / (5 * L / 6) := by
  dsimp only
  have hL0 : 0 < L := by linarith only [hL]
  have hp := mul_inv_cancel₀ Real.pi_ne_zero
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  linear_combination (Real.exp (L * (2 : ℝ)⁻¹) * (6 / 5) * L⁻¹) * hp

/-- Above 97/5, the canonical width meets the smoothing and zero-cutoff conditions. -/
theorem integrated_smoothing_conditions {L : ℝ} (hL : (97 / 5 : ℝ) ≤ L) :
    let s := Real.exp (L / 2)
    let q := 5 * L / (6 * Real.pi)
    let δ := q / s
    0 < δ ∧ δ ≤ 1 / 2 ∧ 100 ≤ 2 / δ ∧ 1 < Real.exp L - Real.exp L * δ := by
  dsimp only
  let s := Real.exp (L / 2)
  let q := 5 * L / (6 * Real.pi)
  let δ := q / s
  change 0 < δ ∧ δ ≤ 1 / 2 ∧ 100 ≤ 2 / δ ∧ 1 < Real.exp L - Real.exp L * δ
  have hs : 0 < s := Real.exp_pos _
  have hc := integrated_scale_conditions hL
  change 0 < q ∧ 4 ≤ q ∧ 16000 ≤ s ∧ δ ≤ 1 / 2000 ∧ 4000 ≤ 2 / δ at hc
  have hδ : 0 < δ := div_pos hc.1 hs
  have hexp : Real.exp L = s ^ 2 := by
    dsimp only [s]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hp := mul_le_mul_of_nonneg_left hc.2.2.2.1 (sq_nonneg s)
  have hsq := sq_nonneg (s - 16000)
  have hleft : 1 < Real.exp L - Real.exp L * δ := by
    rw [hexp]
    nlinarith only [hp, hc.2.2.1, hsq]
  exact ⟨hδ, by linarith only [hc.2.2.2.1], by linarith only [hc.2.2.2.2], hleft⟩

/-- Under RH and the stated reciprocal-zero constant bound, the normalized
ψ error at exp L is at most the integrated envelope for L at least 97/5. -/
theorem psi_le_integrated_envelope (hRH : RiemannHypothesis)
    (hC : zeroReciprocalConstant ≤ -(317 / 10000 : ℝ)) {L : ℝ} (hL : (97 / 5 : ℝ) ≤ L) :
    |Chebyshev.psi (Real.exp L) - Real.exp L| / Real.exp (L / 2) ≤ integratedPsiEnvelope L := by
  let s := Real.exp (L / 2)
  let q := 5 * L / (6 * Real.pi)
  let δ := q / s
  have hs : s ≠ 0 := (Real.exp_pos _).ne'
  have hL0 : 0 < L := by linarith only [hL]
  have hsi := inv_mul_cancel₀ hs
  have halg : (2 / δ) / (2 * Real.pi) = s / (5 * L / 6) := integrated_cutoff_log_arg hL
  have hsq : s * δ = q := by
    dsimp only [δ]
    simp only [div_eq_mul_inv]
    linear_combination q * hsi
  have hrem : 1 / (Real.exp L * δ * s) = 1 / (q * Real.exp L) := by
    have h : Real.exp L * δ * s = q * Real.exp L := by
      dsimp only [δ]
      simp only [div_eq_mul_inv]
      linear_combination (Real.exp L * q) * hsi
    rw [h]
  have hlog : Real.log (s / (5 * L / 6)) = L / 2 - Real.log (5 * L / 6) := by
    rw [Real.log_div hs
        (div_ne_zero (mul_ne_zero (by norm_num only) hL0.ne') (by norm_num only : (6 : ℝ) ≠ 0))]
    dsimp only [s]
    rw [Real.log_exp]
  have hc := integrated_smoothing_conditions hL
  change 0 < δ ∧ δ ≤ 1 / 2 ∧ 100 ≤ 2 / δ ∧ 1 < Real.exp L - Real.exp L * δ at hc
  have h := psi_error_integrated_of_constant hRH (Real.exp_pos L) hc.1 hc.2.1 hc.2.2.2 hc.2.2.1 hC
  rw [← Real.exp_half] at h
  change
    |Chebyshev.psi (Real.exp L) - Real.exp L| / s ≤
      s * δ / 2 + Real.log (2 * Real.pi) / s +
        (1 + δ) *
          (((Real.log ((2 / δ) / (2 * Real.pi))) ^ 2 + 2 * Real.log ((2 / δ) / (2 * Real.pi)) + 2) /
                (2 * Real.pi) -
              317 / 10000 +
            ((29 / 27 : ℝ) * (16 + (7 / 5 : ℝ) * Real.log (2 / δ)) +
                (7 / 5 : ℝ) * (37 / 162 + 2 * Real.log 3 / 27) +
                1 / 10) /
              (2 / δ) ^ 2) +
        1 / (Real.exp L * δ * s) at h
  rw [halg, hlog, hsq, hrem] at h
  dsimp only [integratedPsiEnvelope]
  change
    _ ≤
      q / 2 +
        (1 + δ) *
          (((L / 2 - Real.log (5 * L / 6)) ^ 2 + 2 * (L / 2 - Real.log (5 * L / 6)) + 2) /
                (2 * Real.pi) -
              317 / 10000 +
            ((29 / 27 : ℝ) * (16 + (7 / 5 : ℝ) * Real.log (2 / δ)) +
                (7 / 5 : ℝ) * (37 / 162 + 2 * Real.log 3 / 27) +
                1 / 10) /
              (2 / δ) ^ 2) +
        Real.log (2 * Real.pi) / s +
        1 / (q * Real.exp L)
  linarith only [h]

/-- Under RH and the stated reciprocal-zero constant bound, the normalized
ψ error at x is bounded by the integrated envelope, which is at least 1/200
below the Lee–Nosal target. -/
theorem psi_integrated_envelope_of_constant (hRH : RiemannHypothesis)
    (hC : zeroReciprocalConstant ≤ -(317 / 10000 : ℝ)) {x : ℝ} (hx : 0 < x)
    (hL : (97 / 5 : ℝ) ≤ Real.log x) :
    |Chebyshev.psi x - x| / Real.sqrt x ≤ integratedPsiEnvelope (Real.log x) ∧
      integratedPsiEnvelope (Real.log x) ≤ leeNosalPsiLog (Real.log x) - 1 / 200 := by
  constructor
  · have h := psi_le_integrated_envelope hRH hC hL
    rw [Real.exp_log hx, Real.exp_half, Real.exp_log hx] at h
    exact h
  · exact integrated_envelope_le_target hL

/-- Under RH and the explicit height-100 count and reciprocal-sum
conditions, the integrated envelope gives the stated double inequality. -/
theorem psi_integrated_envelope_of_head (hRH : RiemannHypothesis) (hc : zeroCount 100 = 58)
    (hs : zeroReciprocalSum 100 ≤ (11846 / 10000 : ℝ)) {x : ℝ} (hx : 0 < x)
    (hL : (97 / 5 : ℝ) ≤ Real.log x) :
    |Chebyshev.psi x - x| / Real.sqrt x ≤ integratedPsiEnvelope (Real.log x) ∧
      integratedPsiEnvelope (Real.log x) ≤ leeNosalPsiLog (Real.log x) - 1 / 200 := by
  exact psi_integrated_envelope_of_constant hRH (zeroReciprocalConstant_le_sharp hRH hc hs) hx hL

/-- Under RH, 29 ordered zeros in the stated lower brackets and the
height-100 count bound imply the integrated-envelope double inequality. -/
theorem psi_integrated_envelope_of_brackets (hRH : RiemannHypothesis) (g : Fin 29 → ℝ)
    (hmono : StrictMono g) (hpos : ∀ i, 0 < g i) (hheight : ∀ i, g i ≤ 100)
    (hzero : ∀ i, riemannZeta (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I) = 0)
    (hcount : zeroCount 100 ≤ 58) (hl : LowZero100LowerBounds g) {x : ℝ} (hx : 0 < x)
    (hL : (97 / 5 : ℝ) ≤ Real.log x) :
    |Chebyshev.psi x - x| / Real.sqrt x ≤ integratedPsiEnvelope (Real.log x) ∧
      integratedPsiEnvelope (Real.log x) ≤ leeNosalPsiLog (Real.log x) - 1 / 200 := by
  exact
    psi_integrated_envelope_of_constant hRH
      (zeroReciprocalConstant_sharp_of_brackets hRH g hmono hpos hheight hzero hcount hl) hx hL

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
