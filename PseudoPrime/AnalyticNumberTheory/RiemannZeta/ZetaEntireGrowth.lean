/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCount
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.VerticalGrowth

/-!
# Growth of pole-cancelled zeta on `Re s > -1`

The entire function `zetaEntire(s) = (s-1)ζ(s)`, patched to one at `s=1`,
cancels the pole term in the sawtooth bound for zeta. The triangle inequality
then bounds it by a polynomial in `‖s‖` with coefficients depending on `Re s`.
This is the zeta factor in `ξ(s)=π^(-s/2)Γ(s/2+1)zetaEntire(s)`.
-/

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- A polynomial-in-`‖s‖` growth bound for `PseudoPrime.AnalyticNumberTheory.RiemannZeta.zetaEntire`
on `Re s > -1`, uniform in `Im s`: the pole
of `riemannZeta` at `s = 1` that forced the exclusion `s ≠ 1` in
`PseudoPrime.AnalyticNumberTheory.RiemannZeta.norm_riemannZeta_le_of_reGt_neg_one_diff_one` is
exactly cancelled by the `(s - 1)` factor in
`PseudoPrime.AnalyticNumberTheory.RiemannZeta.zetaEntire`,
and separately checked at the patched point `s = 1` itself. -/
theorem norm_zetaEntire_le_of_reGt_neg_one {s : ℂ} (hs : -1 < s.re) :
    ‖zetaEntire s‖ ≤ ‖s‖ + (‖s‖ + 1) / 2 + ‖s‖ * (‖s‖ + 1) ^ 2 * sawtoothRemainderBound s.re := by
  have hsawnn : 0 ≤ sawtoothRemainderBound s.re := sawtoothRemainderBound_nonneg s.re
  rcases eq_or_ne s 1 with rfl | hne
  · have hz1 : zetaEntire (1 : ℂ) = 1 := by simp only [zetaEntire, Function.update_self]
    rw [hz1, norm_one]
    nlinarith [norm_nonneg (1 : ℂ)]
  · have hzeq : zetaEntire s = (s - 1) * riemannZeta s := by
      simp only [zetaEntire, Function.update_of_ne hne]
    have hsm1_ne : s - 1 ≠ 0 := sub_ne_zero.mpr hne
    have hsm1_pos : 0 < ‖s - 1‖ := norm_pos_iff.mpr hsm1_ne
    have hζ :
      ‖riemannZeta s‖ ≤ ‖s‖ / ‖s - 1‖ + 1 / 2 + ‖s‖ * (‖s‖ + 1) * sawtoothRemainderBound s.re :=
      norm_riemannZeta_le_of_reGt_neg_one_diff_one ⟨hs, hne⟩
    have hstep1 :
      ‖zetaEntire s‖ ≤
        ‖s - 1‖ * (‖s‖ / ‖s - 1‖ + 1 / 2 + ‖s‖ * (‖s‖ + 1) * sawtoothRemainderBound s.re) := by
      rw [hzeq, norm_mul]
      exact mul_le_mul_of_nonneg_left hζ (norm_nonneg _)
    have hexpand :
      ‖s - 1‖ * (‖s‖ / ‖s - 1‖ + 1 / 2 + ‖s‖ * (‖s‖ + 1) * sawtoothRemainderBound s.re) =
        ‖s‖ + ‖s - 1‖ / 2 + ‖s - 1‖ * (‖s‖ * (‖s‖ + 1) * sawtoothRemainderBound s.re) := by
      rw [mul_add, mul_add, mul_div_cancel₀ _ hsm1_pos.ne']
      ring
    rw [hexpand] at hstep1
    have hsm1_le : ‖s - 1‖ ≤ ‖s‖ + 1 := by
      calc
        ‖s - 1‖ ≤ ‖s‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = ‖s‖ + 1 := by rw [norm_one]
    have hnn : 0 ≤ ‖s‖ * (‖s‖ + 1) * sawtoothRemainderBound s.re := by positivity
    calc
      ‖zetaEntire s‖ ≤
          ‖s‖ + ‖s - 1‖ / 2 + ‖s - 1‖ * (‖s‖ * (‖s‖ + 1) * sawtoothRemainderBound s.re) :=
        hstep1
      _ ≤ ‖s‖ + (‖s‖ + 1) / 2 + (‖s‖ + 1) * (‖s‖ * (‖s‖ + 1) * sawtoothRemainderBound s.re) := by
        gcongr
      _ = ‖s‖ + (‖s‖ + 1) / 2 + ‖s‖ * (‖s‖ + 1) ^ 2 * sawtoothRemainderBound s.re := by ring

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
