/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.RiemannXi.Basic

/-!
# Xi growth by reflection

A monotone norm envelope on `Re s ≥ 1/2` extends to the whole plane via
`ξ(1-s)=ξ(s)` and `‖1-s‖ ≤ ‖s‖+1`. The Gamma/zeta factorization supplies
the right-half-plane input.
-/

namespace PseudoPrime.AnalyticNumberTheory.RiemannXi

/-- If `bound` dominates `‖PseudoPrime.AnalyticNumberTheory.RiemannXi.riemannXi s‖` for every `s`
with `Re s ≥ 1/2`, and `bound` is monotone
on `[0, ∞)` (the only region its argument `‖s‖` ever ranges over), then `bound (‖s‖ + 1)` dominates
`‖PseudoPrime.AnalyticNumberTheory.RiemannXi.riemannXi s‖` for *every* `s : ℂ`. The `+ 1` slack
absorbs the `‖1 - s‖ ≤ ‖s‖ + 1`
triangle-inequality loss incurred when reflecting a left half-plane point `s` to the right
half-plane point `1 - s` via `PseudoPrime.AnalyticNumberTheory.RiemannXi.riemannXi_one_sub`. -/
theorem norm_riemannXi_le_of_forall_one_half_le_re {bound : ℝ → ℝ}
    (hbound_mono : MonotoneOn bound (Set.Ici 0))
    (h :
      ∀ s : ℂ, 1 / 2 ≤ s.re → ‖riemannXi s‖ ≤ bound ‖s‖)
    (s : ℂ) : ‖riemannXi s‖ ≤ bound (‖s‖ + 1) := by
  by_cases hs : 1 / 2 ≤ s.re
  · exact
      (h s hs).trans
        (hbound_mono (norm_nonneg s) (Set.mem_Ici.mpr (by positivity))
          (by linarith [norm_nonneg s]))
  · rw [not_le] at hs
    have hs' : 1 / 2 ≤ (1 - s).re := by
      simp only [Complex.sub_re, Complex.one_re]; linarith
    have h1 : ‖riemannXi (1 - s)‖ ≤ bound ‖1 - s‖ :=
      h (1 - s) hs'
    rw [riemannXi_one_sub] at h1
    have habs : ‖(1 : ℂ) - s‖ ≤ ‖s‖ + 1 := by
      calc
        ‖(1 : ℂ) - s‖ ≤ ‖(1 : ℂ)‖ + ‖s‖ := norm_sub_le _ _
        _ = ‖s‖ + 1 := by
          rw [norm_one]; ring
    exact h1.trans (hbound_mono (norm_nonneg _) (Set.mem_Ici.mpr (by positivity)) habs)

/-- For `s ≠ 1` and `Γ(s/2+1) ≠ 0`, xi equals
`π^(-s/2) Γ(s/2+1) zetaEntire(s)`. This form separates the three factors
used in the right-half-plane growth bound. -/
theorem riemannXi_eq_gamma_mul_zetaEntire {s : ℂ} (hs1 : s ≠ 1)
    (hΓne : Complex.Gamma (s / 2 + 1) ≠ 0) :
    riemannXi s =
      (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2 + 1) *
        RiemannZeta.zetaEntire s := by
  have hdenom_ne : 2 * (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2 + 1) ≠ 0 := by
    have hpow_ne : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    exact mul_ne_zero (mul_ne_zero two_ne_zero hpow_ne) hΓne
  have hnum :
    riemannZeta s * (2 * (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2 + 1)) =
      s * completedRiemannZeta₀ s - 1 - s / (1 - s) :=
    (eq_div_iff hdenom_ne).mp (riemannZeta_eq_mul_completedRiemannZeta₀ s)
  have hxi := riemannXi_eq hs1
  rw [← hnum] at hxi
  have hz :
    RiemannZeta.zetaEntire s = (s - 1) * riemannZeta s := by
    simp only [RiemannZeta.zetaEntire, Function.update_of_ne hs1]
  rw [hxi, hz]
  ring

end PseudoPrime.AnalyticNumberTheory.RiemannXi
