/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevIntegralMain194Numerics
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.IntegratedZeroRemainder194

/-! # Canonical scale for the integrated ψ envelope -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The integrated normalized ψ envelope at logarithmic height L.
The cut-off is twice the reciprocal relative smoothing width, and the last
term is the reciprocal-width contribution. -/
noncomputable def integratedPsiEnvelope (L : ℝ) : ℝ :=
  let s := Real.exp (L / 2)
  let q := 5 * L / (6 * Real.pi)
  let δ := q / s
  let T := 2 / δ
  let a := L / 2 - Real.log (5 * L / 6)
  q / 2 +
    (1 + δ) *
      ((a ^ 2 + 2 * a + 2) / (2 * Real.pi) - 317 / 10000 +
        ((29 / 27 : ℝ) * (16 + (7 / 5 : ℝ) * Real.log T) +
            (7 / 5 : ℝ) * (37 / 162 + 2 * Real.log 3 / 27) +
            1 / 10) /
          T ^ 2) +
    Real.log (2 * Real.pi) / s +
    1 / (q * Real.exp L)

/-- Above 97/5, the canonical smoothing width is positive, at most
1/2000, and its cutoff is at least 4000. The exponential at the endpoint
also bounds the inverse-width remainder. -/
theorem integrated_scale_conditions {L : ℝ} (hL : (97 / 5 : ℝ) ≤ L) :
    let s := Real.exp (L / 2)
    let q := 5 * L / (6 * Real.pi)
    0 < q ∧ 4 ≤ q ∧ 16000 ≤ s ∧ q / s ≤ 1 / 2000 ∧ 4000 ≤ 2 / (q / s) := by
  dsimp only
  let s := Real.exp (L / 2)
  let q := 5 * L / (6 * Real.pi)
  have hL0 : 0 < L := by linarith only [hL]
  have hs : 0 < s := Real.exp_pos _
  have hp : 0 < Real.pi := Real.pi_pos
  have hq : 0 < q := div_pos (mul_pos (by norm_num only) hL0) (mul_pos (by norm_num only) hp)
  have hq4 : 4 ≤ q := by
    dsimp only [q]
    apply (le_div_iff₀ (mul_pos (by norm_num only : (0 : ℝ) < 6) hp)).2
    nlinarith only [hL, Real.pi_lt_four]
  have hq3 : q ≤ L / 3 := by
    dsimp only [q]
    apply (div_le_iff₀ (mul_pos (by norm_num only : (0 : ℝ) < 6) hp)).2
    have hm := mul_nonneg hL0.le (show 0 ≤ Real.pi - 3 by linarith only [Real.pi_gt_d4])
    nlinarith only [hm, hL0]
  have hsmin : 16000 ≤ s := by
    change 16000 ≤ Real.exp (L / 2)
    exact exp_97_over_10_ge_16000.trans (Real.exp_le_exp.mpr (by linarith only [hL]))
  have htangent := Real.add_one_le_exp (L / 2 - 97 / 10)
  have hm :=
    mul_le_mul exp_97_over_10_ge_16000 htangent
      (by linarith only [hL] : (0 : ℝ) ≤ L / 2 - 97 / 10 + 1) (Real.exp_pos (97 / 10)).le
  have hexp : s = Real.exp (97 / 10) * Real.exp (L / 2 - 97 / 10) := by
    dsimp only [s]
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← hexp] at hm
  have hs700 : 700 * L ≤ s := by nlinarith only [hm, hL]
  have hδ : q / s ≤ 1 / 2000 := by
    apply (div_le_iff₀ hs).2
    nlinarith only [hs700, hq3, hL0]
  have hδpos : 0 < q / s := div_pos hq hs
  have hcut : 4000 ≤ 2 / (q / s) := by
    apply (le_div_iff₀ hδpos).2
    linarith only [hδ]
  exact ⟨hq, hq4, hsmin, hδ, hcut⟩

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
