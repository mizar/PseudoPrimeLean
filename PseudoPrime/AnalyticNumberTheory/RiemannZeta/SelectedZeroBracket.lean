/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.SelectedZeroPairs

/-! # Selected conjugate pairs from critical-line zero brackets -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The critical-line point has its prescribed imaginary coordinate.
This transfers real interval bounds to the conjugate-pair interface. -/
private theorem bracket_point_im (t : ℝ) : ((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).im = t := by
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
    Complex.I_im, mul_one, mul_zero, add_zero, zero_add]

/-- Every critical-line point has nonnegative real coordinate.
The real coordinate is exactly one half, as required by zero-ledger membership. -/
private theorem bracket_point_re (t : ℝ) : 0 ≤ ((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re := by
  norm_num only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]

/-- A critical-line zero above height one hundred supplies an admissible conjugate pair.
The cutoff bound gives ledger membership and an explicit unweighted moment bound, without RH. -/
theorem critical_pair_of_zero {t b T : ℝ} (hi : 100 < t) (ht : t ≤ b) (hT : b ≤ T)
    (hz : riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) = 0) :
    ∃ Q : Finset ℂ,
      Q.card = 2 ∧
        Q ⊆ zerosUpTo T ∧
        (∀ ρ ∈ Q, 100 < |ρ.im|) ∧ (∑ ρ ∈ Q, (|ρ.im| + 1 / 2)) ≤ 2 * (b + 1 / 2) := by
  classical
  let ρ : ℂ := ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I
  have hp : 100 < ρ.im := (bracket_point_im t).symm ▸ hi
  have hu : ρ.im ≤ b := (bracket_point_im t).symm ▸ ht
  exact
    ⟨{ρ, (starRingEnd ℂ) ρ}, Finset.card_pair (conjugate_pair_ne hp),
      conjugate_pair_subset hz (bracket_point_re t) hp (hu.trans hT), conjugate_pair_above hp,
      conjugate_pair_moment hp hu⟩

/-- A zero in an open interval above height one hundred supplies a selected pair.
Extract its ordinate and apply the critical-line pair theorem.
No simplicity or completeness assumption is used. -/
theorem selected_pair_of_interval_zero {a b T : ℝ} (ha : 100 ≤ a) (hT : b ≤ T)
    (hz : ∃ t ∈ Set.Ioo a b, riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) = 0) :
    ∃ Q : Finset ℂ,
      Q.card = 2 ∧
        Q ⊆ zerosUpTo T ∧
        (∀ ρ ∈ Q, 100 < |ρ.im|) ∧ (∑ ρ ∈ Q, (|ρ.im| + 1 / 2)) ≤ 2 * (b + 1 / 2) := by
  obtain ⟨t, ht, hzero⟩ := hz
  exact critical_pair_of_zero (ha.trans_lt ht.1) ht.2.le hT hzero

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
