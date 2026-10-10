/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannXi.ZeroFiniteness
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.HeightSequence
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LogDerivBound

/-! # Zeta good heights avoid both signed xi zero ordinates

Every xi zero is a zeta zero, and xi reflection exchanges the two signed heights.
This supplies horizontal nonvanishing for principal-character contour ledgers.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannXi

/-- Every ξ zero avoids both the positive zeta good height and its negative.
For the upper height, apply zeta nonvanishing to the xi-to-zeta zero inclusion.
For the lower height, reflect the xi zero through `s ↦ 1-s`. No RH is required;
the result keeps horizontal boundaries disjoint from the finite residue ledger. -/
theorem zero_im_ne_goodHeight (n : ℕ) {s : ℂ} (hs : riemannXi s = 0) :
    s.im ≠ RiemannZeta.goodHeightSeq n ∧ s.im ≠ -RiemannZeta.goodHeightSeq n := by
  have hu {z : ℂ} (hz : riemannXi z = 0) : z.im ≠ RiemannZeta.goodHeightSeq n := by
    intro hi
    have he : z = (z.re : ℂ) + RiemannZeta.goodHeightSeq n * Complex.I := by
      apply Complex.ext
      · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
      · simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im, Complex.I_re,
          Complex.ofReal_re, mul_one, mul_zero, add_zero, zero_add] using hi
    have hζ := riemannZeta_zero_of_riemannXi_zero hz
    rw [he] at hζ
    exact
      RiemannZeta.riemannZeta_ne_zero_of_good_height (le_add_of_nonneg_right (Nat.cast_nonneg n))
        (RiemannZeta.goodHeightSeq_mem n) (RiemannZeta.goodHeightSeq_good n) z.re hζ
  refine ⟨hu hs, ?_⟩
  intro hi
  have hz : riemannXi (1 - s) = 0 := by rw [riemannXi_one_sub, hs]
  apply hu hz
  rw [Complex.sub_im, Complex.one_im, hi, sub_neg_eq_add, zero_add]

end PseudoPrime.AnalyticNumberTheory.RiemannXi
