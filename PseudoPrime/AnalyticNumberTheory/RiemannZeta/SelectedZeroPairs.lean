/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeightCounting
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic.Ring

/-! # Conjugate pairs for finite selected-zero budgets -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- A zero with imaginary part above 100 is distinct from its conjugate.
Comparing imaginary parts supplies the nonduplication condition for pair sums. -/
theorem conjugate_pair_ne {ρ : ℂ} (hi : 100 < ρ.im) : ρ ≠ (starRingEnd ℂ) ρ := by
  intro h
  have hh := congrArg Complex.im h
  rw [Complex.conj_im] at hh
  linarith only [hi, hh]

/-- A conjugate pair of zeta zeros with nonnegative real part and positive
height at most T belongs to the finite height ledger. No RH assumption is needed;
this turns actual critical-line brackets into admissible selected copies. -/
theorem conjugate_pair_subset {ρ : ℂ} {T : ℝ} (hz : riemannZeta ρ = 0) (hre : 0 ≤ ρ.re)
    (hi : 100 < ρ.im) (ht : ρ.im ≤ T) : ({ρ, (starRingEnd ℂ) ρ} : Finset ℂ) ⊆ zerosUpTo T := by
  classical
  have hpos : 0 < ρ.im := lt_trans (by norm_num only) hi
  have ht0 : 0 ≤ T := hpos.le.trans ht
  have hp : ρ ∈ zerosUpTo T :=
    (mem_zerosUpTo ht0).mpr
      ⟨hz, hre, by
        rw [abs_of_pos hpos]; exact ht⟩
  have hn : (starRingEnd ℂ) ρ ∈ zerosUpTo T := by
    apply (mem_zerosUpTo ht0).mpr
    rw [riemannZeta_conj, hz, map_zero, Complex.conj_re, Complex.conj_im, abs_neg, abs_of_pos hpos]
    exact ⟨rfl, hre, ht⟩
  intro z hz
  rcases Finset.mem_insert.mp hz with h | h
  · exact h ▸ hp
  · exact (Finset.mem_singleton.mp h) ▸ hn

/-- The unweighted ordinate moment of a selected conjugate pair is bounded
by twice T+1/2 when its positive height is at most T. Distinctness prevents
collapsing the pair and supplies the selected curvature budget. -/
theorem conjugate_pair_moment {ρ : ℂ} {T : ℝ} (hi : 100 < ρ.im) (ht : ρ.im ≤ T) :
    ∑ z ∈ ({ρ, (starRingEnd ℂ) ρ} : Finset ℂ), (|z.im| + 1 / 2) ≤ 2 * (T + 1 / 2) := by
  classical
  rw [Finset.sum_pair (conjugate_pair_ne hi), Complex.conj_im, abs_neg,
    abs_of_pos (lt_trans (by norm_num only) hi)]
  linarith only [ht]

/-- Both members of a conjugate pair have absolute ordinate above 100
when its positive ordinate is above 100. This discharges the selected band's
strict lower-height hypothesis without multiplicity or simplicity assumptions. -/
theorem conjugate_pair_above {ρ : ℂ} (hi : 100 < ρ.im) :
    ∀ z ∈ ({ρ, (starRingEnd ℂ) ρ} : Finset ℂ), 100 < |z.im| := by
  classical
  intro z hz
  rcases Finset.mem_insert.mp hz with h | h
  · subst z
    rw [abs_of_pos (lt_trans (by norm_num only) hi)]
    exact hi
  · rw [Finset.mem_singleton.mp h, Complex.conj_im, abs_neg,
      abs_of_pos (lt_trans (by norm_num only) hi)]
    exact hi

/-- The real normalized phase quotient is invariant under conjugation.
Conjugation negates the ordinate and the imaginary exponential factor, giving
the same real part. This permits pairing selected copies before scalar evaluation. -/
theorem re_phase_div_conj (ρ : ℂ) (v : ℝ) :
    (Complex.exp (((((starRingEnd ℂ) ρ).im * v : ℝ) : ℂ) * Complex.I) / ((starRingEnd ℂ) ρ)).re =
      (Complex.exp (((ρ.im * v : ℝ) : ℂ) * Complex.I) / ρ).re := by
  have hang :
    (((((starRingEnd ℂ) ρ).im * v : ℝ) : ℂ) * Complex.I) =
      (starRingEnd ℂ) (((ρ.im * v : ℝ) : ℂ) * Complex.I) := by
    rw [Complex.conj_im, neg_mul, Complex.ofReal_neg, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [hang, Complex.exp_conj, ← map_div₀, Complex.conj_re]

/-- A selected conjugate pair contributes exactly twice the reciprocal positive
ordinate. The formula feeds the subtraction from the residual zero budget. -/
theorem conjugate_pair_reciprocal {ρ : ℂ} (hi : 100 < ρ.im) :
    (∑ z ∈ ({ρ, (starRingEnd ℂ) ρ} : Finset ℂ), 1 / |z.im|) = 2 / ρ.im := by
  classical
  rw [Finset.sum_pair (conjugate_pair_ne hi), Complex.conj_im, abs_neg,
    abs_of_pos (lt_trans (by norm_num only) hi)]
  ring

/-- A selected conjugate pair contributes twice the real positive-height phase
quotient. No multiplicity or completeness assertion is needed; this is the
signed scalar phase used by the finite selected-zero checker. -/
theorem conjugate_pair_phase {ρ : ℂ} (hi : 100 < ρ.im) (v : ℝ) :
    (∑ z ∈ ({ρ, (starRingEnd ℂ) ρ} : Finset ℂ),
          Complex.exp (((z.im * v : ℝ) : ℂ) * Complex.I) / z).re =
      2 * (Complex.exp (((ρ.im * v : ℝ) : ℂ) * Complex.I) / ρ).re := by
  classical
  rw [Finset.sum_pair (conjugate_pair_ne hi), Complex.add_re, re_phase_div_conj]
  ring

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
