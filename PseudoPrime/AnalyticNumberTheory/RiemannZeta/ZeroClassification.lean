/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCount
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCounting

/-!
# Common bookkeeping for zeta zeros

RH zero classification and natural-number indices for trivial zeros, independent
of contour estimates and xi-zero transfer.
-/

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Under RH, every zeta zero with nonnegative real part lies on `Re s = 1/2`. -/
theorem riemannZeta_zero_re_eq_half_of_riemannHypothesis (hRH : RiemannHypothesis) {ρ : ℂ}
    (hρ : riemannZeta ρ = 0) (hre : 0 ≤ ρ.re) : ρ.re = 1 / 2 := by
  have hne1 : ρ ≠ 1 := by
    intro h
    rw [h] at hρ
    exact riemannZeta_one_ne_zero hρ
  have hntrivial : ¬∃ n : ℕ, ρ = -2 * ((n : ℂ) + 1) := by
    rintro ⟨n, hn⟩
    have hn' : ρ = ((-(2 * ((n : ℝ) + 1)) : ℝ) : ℂ) := by
      rw [hn]; push_cast; ring
    rw [hn', Complex.ofReal_re] at hre
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  exact hRH ρ hρ hntrivial hne1

/-- Under RH, a nontrivial zeta zero satisfies `normSq (ρ - 1) = normSq ρ`. -/
theorem normSq_riemannZeta_zero_sub_one_eq_of_riemannHypothesis (hRH : RiemannHypothesis) {ρ : ℂ}
    (hρ : riemannZeta ρ = 0) (hre : 0 ≤ ρ.re) : Complex.normSq (ρ - 1) = Complex.normSq ρ := by
  have hhalf :=
    riemannZeta_zero_re_eq_half_of_riemannHypothesis
      hRH hρ hre
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
  rw [hhalf]
  ring

/-- Every zeta zero with negative real part is a trivial zero `-2(k+1)`. -/
theorem exists_nat_eq_neg_two_mul_add_one_of_riemannZeta_zero_re_neg {w : ℂ} (hw : w.re < 0)
    (hz : riemannZeta w = 0) : ∃ n : ℕ, w = -2 * ((n : ℂ) + 1) := by
  by_contra h
  push Not at h
  exact riemannZeta_ne_zero_of_re_neg hw h hz

/-- A choice of the natural-number index of a trivial zero; arbitrary away from trivial zeros. -/
noncomputable def trivialZeroIndex (ρ : ℂ) : ℕ := by
  classical exact if h : ∃ n : ℕ, ρ = -2 * ((n : ℂ) + 1) then h.choose else 0

/-- The chosen `PseudoPrime.AnalyticNumberTheory.RiemannZeta.trivialZeroIndex` reconstructs
any known trivial zero. -/
theorem trivialZeroIndex_spec {ρ : ℂ} (h : ∃ n : ℕ, ρ = -2 * ((n : ℂ) + 1)) :
    ρ = -2 * ((trivialZeroIndex ρ : ℂ) + 1) := by
  unfold trivialZeroIndex
  rw [dite_eq_left h]
  exact h.choose_spec

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
