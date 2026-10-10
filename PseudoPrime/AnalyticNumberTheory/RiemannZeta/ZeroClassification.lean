/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCount
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCounting

/-!
# Common bookkeeping for zeta zeros

RH zero classification and natural-number indices for trivial zeros, independent
of contour estimates and xi-zero transfer.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Assuming RH, a zeta zero `ρ` with `Re ρ ≥ 0` has real part one half.
Nonnegative real part excludes the negative even trivial zeros, while zeta's nonzero
totalized value at one excludes that point. This supplies the critical-line form for zero weights.
-/
theorem riemannZeta_zero_re_eq_half_of_riemannHypothesis (hRH : RiemannHypothesis) {ρ : ℂ}
    (hρ : riemannZeta ρ = 0) (hre : 0 ≤ ρ.re) : ρ.re = 1 / 2 := by
  have hne1 : ρ ≠ 1 := by
    intro h
    rw [h] at hρ
    exact riemannZeta_one_ne_zero hρ
  have hntrivial : ¬∃ n : ℕ, ρ = -2 * ((n : ℂ) + 1) := by
    rintro ⟨n, hn⟩
    have hn' : ρ = ((-(2 * ((n : ℝ) + 1)) : ℝ) : ℂ) := by
      rw [hn]
      push_cast
      ring
    rw [hn', Complex.ofReal_re] at hre
    nlinarith only [hre, Nat.cast_nonneg (α := ℝ) n]
  exact hRH ρ hρ hntrivial hne1

/-- Assuming RH, a zeta zero with nonnegative real part satisfies
`normSq (ρ - 1) = normSq ρ`. Expand both squared norms and substitute `Re ρ = 1/2`.
This identifies the two denominator sizes in reciprocal contour zero contributions. -/
theorem normSq_riemannZeta_zero_sub_one_eq_of_riemannHypothesis (hRH : RiemannHypothesis) {ρ : ℂ}
    (hρ : riemannZeta ρ = 0) (hre : 0 ≤ ρ.re) : Complex.normSq (ρ - 1) = Complex.normSq ρ := by
  have hhalf := riemannZeta_zero_re_eq_half_of_riemannHypothesis hRH hρ hre
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
  rw [hhalf]
  ring

/-- If `Re w < 0` and `ζ(w) = 0`, then `w = -2*(n+1)` for some natural `n`.
Otherwise the zero-free negative-half-plane theorem away from trivial zeros contradicts
the zero assertion. This separates the trivial-zero branch of finite residue ledgers. -/
theorem exists_nat_eq_neg_two_mul_add_one_of_riemannZeta_zero_re_neg {w : ℂ} (hw : w.re < 0)
    (hz : riemannZeta w = 0) : ∃ n : ℕ, w = -2 * ((n : ℂ) + 1) := by
  by_contra h
  push Not at h
  exact riemannZeta_ne_zero_of_re_neg hw h hz

/-- For a complex `ρ`, choose `n` with `ρ = -2*(n+1)` when such an index exists, and
return zero otherwise. The selected index reconstructs every known trivial zero via the
specification theorem below, allowing its contribution to be indexed by naturals. -/
noncomputable def trivialZeroIndex (ρ : ℂ) : ℕ := by
  classical exact if h : ∃ n : ℕ, ρ = -2 * ((n : ℂ) + 1) then h.choose else 0

/-- Given an index witnessing that `ρ` is a negative even trivial-zero location,
`trivialZeroIndex ρ` reconstructs `ρ` as `-2*(index+1)`. Unfold the positive branch of the
choice definition and use its witness specification. This justifies natural-index residue sums. -/
theorem trivialZeroIndex_spec {ρ : ℂ} (h : ∃ n : ℕ, ρ = -2 * ((n : ℂ) + 1)) :
    ρ = -2 * ((trivialZeroIndex ρ : ℂ) + 1) := by
  unfold trivialZeroIndex
  rw [dite_eq_left h]
  exact h.choose_spec

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
