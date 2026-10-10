/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.Growth
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.Analysis.Complex.PhragmenLindelof
public import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
public import Mathlib.NumberTheory.LSeries.AbstractFuncEq
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.BasicBounds

/-!
# Zeta growth and zero-free-region prerequisites

The functional equation gives left-half-plane growth and excludes nontrivial
zeros there. Pole cancellation constructs the entire function `(s-1)ζ(s)`
with value one at the pole. Auxiliary exponential envelopes and Mellin bounds
provide additional strip-growth estimates. The logarithmic local zero count
itself is established separately in `PseudoPrime.AnalyticNumberTheory.RiemannZeta.Jensen`.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- For `Re w < 0`, zeta is nonzero away from the negative even integers.
In the functional equation with `s=1-w`, the factors `2`, `(2π)^(-s)`,
`Γ(s)`, and `ζ(s)` are nonzero. Only `cos(πs/2)` can vanish, forcing
`w=-2(n+1)`. Thus nontrivial zeros cannot lie left of the critical strip. -/
theorem riemannZeta_ne_zero_of_re_neg {w : ℂ} (hw : w.re < 0) (hnt : ∀ n : ℕ, w ≠ -2 * (n + 1)) :
    riemannZeta w ≠ 0 := by
  set s : ℂ := 1 - w with hs_def
  have hs_re : 1 < s.re := by
    rw [hs_def]
    simp only [Complex.sub_re, Complex.one_re]
    exact lt_add_of_pos_right 1 (neg_pos.mpr hw)
  obtain ⟨hs1, hs2⟩ := side_conditions_of_one_lt_re hs_re
  have heq := riemannZeta_one_sub hs1 hs2
  rw [show (1 : ℂ) - s = w from by
      rw [hs_def]
      ring] at heq
  intro hzero
  rw [hzero] at heq
  have h2ne : (2 : ℂ) ≠ 0 := two_ne_zero
  have h2pipos : (0 : ℝ) < 2 * Real.pi := by exact mul_pos (by norm_num only) Real.pi_pos
  have hcpowne : (2 * (Real.pi : ℂ)) ^ (-s) ≠ 0 := by
    intro h
    exact
      (Complex.ofReal_ne_zero.mpr h2pipos.ne')
        (by
          simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat, mul_eq_zero, OfNat.ofNat_ne_zero,
            Complex.ofReal_eq_zero, Real.pi_ne_zero, or_self] using
            ((Complex.cpow_eq_zero_iff _ _).mp h).1)
  have hGammane : Complex.Gamma s ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by exact lt_trans zero_lt_one hs_re)
  have hzetane : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs_re
  have hcosz : Complex.cos ((Real.pi : ℂ) * s / 2) = 0 := by
    have h1 : (2 : ℂ) * (2 * (Real.pi : ℂ)) ^ (-s) * Complex.Gamma s ≠ 0 :=
      mul_ne_zero (mul_ne_zero h2ne hcpowne) hGammane
    rcases mul_eq_zero.mp heq.symm with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' h1
      · exact h'
    · exact absurd h hzetane
  rw [Complex.cos_eq_zero_iff] at hcosz
  obtain ⟨k, hk⟩ := hcosz
  have hseq : s = 2 * (k : ℂ) + 1 := by
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp [hpi] at hk
    linear_combination hk
  have hcomb : (1 : ℂ) - w = 2 * (k : ℂ) + 1 := by
    rw [← hs_def]
    exact hseq
  have hw_eq : w = -2 * (k : ℂ) := by linear_combination -hcomb
  have hwre : w.re = -2 * (k : ℝ) := by
    rw [hw_eq]
    simp only [neg_mul, Complex.neg_re, Complex.mul_re, Complex.re_ofNat, Complex.intCast_re,
      Complex.im_ofNat, Complex.intCast_im, mul_zero, sub_zero]
  have hk0 : (1 : ℤ) ≤ k := by
    have : (-2 : ℝ) * (k : ℝ) < 0 := hwre ▸ hw
    have hkr : (0 : ℝ) < (k : ℝ) := by linarith only [this]
    have : (0 : ℤ) < k := by exact_mod_cast hkr
    exact this
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (by exact sub_nonneg.mpr hk0 : (0 : ℤ) ≤ k - 1)
  have hkn : k = (n : ℤ) + 1 := by linear_combination hn
  have hwval : w = -2 * ((n : ℕ) + 1 : ℂ) := by
    rw [hw_eq, hkn]
    push_cast
    ring
  exact hnt n hwval

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
