/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevIntegratedEnvelope194

/-! # Comparison of the integrated ψ envelope with the Lee–Nosal target -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- For L at least 97/5, the difference between the integrated envelope
and its main term is at most 9/2000. The proof combines the cubic-exponential
bound, the integrated zero-count remainder, and the reciprocal-width term. -/
theorem integrated_envelope_remainder_le {L : ℝ} (hL : (97 / 5 : ℝ) ≤ L) :
    integratedPsiEnvelope L - integratedPsiMain L ≤ (9 / 2000 : ℝ) := by
  let s := Real.exp (L / 2)
  let q := 5 * L / (6 * Real.pi)
  let δ := q / s
  let T := 2 / δ
  let a := L / 2 - Real.log (5 * L / 6)
  let r :=
    ((29 / 27 : ℝ) * (16 + (7 / 5 : ℝ) * Real.log T) +
        (7 / 5 : ℝ) * (37 / 162 + 2 * Real.log 3 / 27) +
        1 / 10) /
      T ^ 2
  have hs : 0 < s := Real.exp_pos _
  have hscale := integrated_scale_conditions hL
  change 0 < q ∧ 4 ≤ q ∧ 16000 ≤ s ∧ δ ≤ 1 / 2000 ∧ 4000 ≤ T at hscale
  have hδ0 : 0 ≤ δ := (div_pos hscale.1 hs).le
  have hr : r ≤ 3 / 1000000 := integrated_zero_remainder_le hscale.2.2.2.2
  have hrd := mul_le_mul_of_nonneg_left hr (show 0 ≤ 1 + δ by linarith only [hδ0])
  have hrd2 : (1 + δ) * r ≤ 6 / 1000000 := by nlinarith only [hrd, hscale.2.2.2.1]
  have hcoef := integrated_remainder_coeff_le hL
  change
    q * ((a ^ 2 + 2 * a + 2) / (2 * Real.pi) - 317 / 10000) + Real.log (2 * Real.pi) ≤
      5 * L ^ 3 / 432 - 5 * L ^ 2 / 108 + 5 * L / 54 + 2 at hcoef
  have hcoef' := mul_le_mul_of_nonneg_right hcoef (inv_nonneg.mpr hs.le)
  have hpoly := integrated_remainder_poly_le hL
  have hsinv : Real.exp (-L / 2) = s⁻¹ := by
    change Real.exp (-L / 2) = (Real.exp (L / 2))⁻¹
    rw [show -L / 2 = -(L / 2) by ring, Real.exp_neg]
  rw [hsinv] at hpoly
  have hsq : (16000 : ℝ) ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ (by norm_num only) hscale.2.2.1 2
  have hexp : Real.exp L = s ^ 2 := by
    dsimp only [s]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hden : (4 : ℝ) * 16000 ^ 2 ≤ q * Real.exp L := by
    rw [hexp]
    exact mul_le_mul hscale.2.1 hsq (by norm_num only) hscale.1.le
  have hsmall := one_div_le_one_div_of_le (by norm_num only : (0 : ℝ) < 4 * 16000 ^ 2) hden
  change integratedPsiEnvelope L - integratedPsiMain L ≤ _
  dsimp only [integratedPsiEnvelope, integratedPsiMain]
  change
    q / 2 + (1 + δ) * ((a ^ 2 + 2 * a + 2) / (2 * Real.pi) - 317 / 10000 + r) +
          Real.log (2 * Real.pi) / s +
          1 / (q * Real.exp L) -
        (q / 2 + (a ^ 2 + 2 * a + 2) / (2 * Real.pi) - 317 / 10000) ≤
      _
  simp only [δ, div_eq_mul_inv, mul_inv_rev] at hcoef' hpoly hrd2 hsmall ⊢
  nlinarith only [hcoef', hpoly, hrd2, hsmall]

/-- For every L at least 97/5, the integrated ψ envelope is at least
1/200 below the Lee–Nosal normalized target. The main-term gap exceeds
19/2000 and the remaining terms are at most 9/2000. -/
theorem integrated_envelope_le_target {L : ℝ} (hL : (97 / 5 : ℝ) ≤ L) :
    integratedPsiEnvelope L ≤ leeNosalPsiLog L - 1 / 200 := by
  have hgap := integrated_main_gap_above_194 hL
  have hrem := integrated_envelope_remainder_le hL
  linarith only [hgap, hrem]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
